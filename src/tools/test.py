"""Run automated tests of program analyzers"""
import random
import sys
import os
import json
import time
import itertools as it
from collections import namedtuple, OrderedDict
from math import ceil
import logging

from ..runner import docker, commands, maze_gen

LOGGER = logging.getLogger(__name__)

REMOVE_CMD = 'rm -r %s'
CP_CMD = 'cp %s %s'
Target = namedtuple(typename='Target',field_names=['maze','tool','index','params','variant','flags'])


def load_config(path):
    with open(path, 'r') as f:
        txt = f.read()
    conf = json.loads(txt)

    if 'verbosity' not in conf.keys():
        conf['verbosity'] = 'all'
    if 'maze_gen' not in conf.keys():
        conf['maze_gen'] = 'local'
    if 'expected_result' not in conf.keys():
        conf['expected_result'] = 'error'
    if 'abort_on_error' not in conf.keys():
        conf['abort_on_error'] = False
    if 'batch_size' not in conf.keys():
        conf['batch_size'] = 1
    if 'gen_time' not in conf.keys():
        conf['gen_time'] = 120

    assert conf['repeats'] != 0
    assert conf['duration'] > 0
    assert conf['workers'] > 0
    assert conf['memory'] > 0
    assert conf['transforms'] >= 0
    assert conf['maze_gen'] in ['local', 'container']
    assert conf['verbosity'] in ['all','summary','bug','bug_only']
    assert conf['expected_result'] in ['error','safe']

    return conf

def pick_values(head: str, value: dict  | list,tail: str) -> str | None:
    if isinstance(value,dict):
        body = str(random.randint(value['min'], value['max']))
    else:
        choice = random.choice(value)
        if choice == 0:
            if head == '' and tail == '':
                return None
            return ''
        elif choice == 1:
            body = ''
        else:
            body = str(choice)
    return head + body + tail

def set_default(parameters, name, value):
    if name not in parameters.keys():
        parameters[name] = value
        LOGGER.debug('Using default value %s for parameter %s', value, name)

def get_random_params(conf):
    conf['repeats'] -= 1
    params = conf['parameters']
    res = {}
    for key, value in params.items():
        if key == 't':
            body = ''
            for tkey, tvalue in value.items():
                transform = pick_values(tkey, tvalue, '_')
                body += transform if transform is not None else ''
            body = body.strip('_') # remove last _
        elif key == 's':
            body = value
            while os.path.isdir(body):
                body = os.path.join(value,random.choice(os.listdir(value)))
        else:
            body = pick_values('', value, '')

        if body is not None:
            res[key] = body

    # default values
    set_default(res,'a','Backtracking')
    set_default(res,'w',5)
    set_default(res,'h',5)
    set_default(res,'b','ve')
    set_default(res,'n',1)
    set_default(res,'t','keepId')
    set_default(res,'r',int(time.time()))
    set_default(res,'c',0)
    set_default(res,'g','default_gen')
    set_default(res,'m',int(conf['transforms']))
    #set_default(res,'u',0) # not included by default

    if 'u' in res:
        res['w'] = 1
        res['h'] = 1
        res['u'] = ''
    elif int(res['w']) < 5 and int(res['h']) < 5:
        res['h'] = 5 # mazelib gets stuck when generating 4x4 or smaller mazes
    return res


class Target_Generator():
    def __init__(self, conf):
        self.conf = conf
        self.repeats = self.conf['repeats'] if self.conf['repeats'] >= 0 else sys.maxsize
        self.targets = list()
        self.mazes = OrderedDict()

    def __iter__(self):
        return self

    def __next__(self):
        if not(self.has_targets()):
            LOGGER.info("All batches generated")
            raise StopIteration
        if len(self.targets) == 0:
            LOGGER.info("Out of targets, fetching new batch.")
            self.add_batch()              
        return self.targets.pop(0)

    def has_targets(self):
        return self.repeats != 0 or len(self.targets) > 0 or len(self.mazes) > 0

    def add_batch(self):
        while(len(self.mazes) < self.conf['batch_size'] and self.repeats != 0):
            LOGGER.info("Out of mazes, generating more.")
            self.generate_mazes()

        self.repeats -= 1

        maze_keys = list(self.mazes.keys())

        batch_id = random.randint(0,65535)
        for tool in self.conf['tool'].keys():
            for i in range(min(len(maze_keys),self.conf['batch_size'])):
                maze = maze_keys[i]
                params = self.mazes[maze]
                variant, flags = self.pick_tool_flags(tool)
                self.targets.append((False,Target(maze, tool,batch_id, params, variant, flags)))
    
        with open(get_batch_file(batch_id), 'w') as batch_file:
            for i in range(min(len(maze_keys),self.conf['batch_size'])):
                batch_file.write(f"{docker.HOST_NAME}/{maze_keys[i]}\n")

        if len(self.targets) > 0:
            self.targets[-1] = (True, self.targets[-1][1])

        for i in range(min(len(maze_keys),self.conf['batch_size'])):
            self.mazes.pop(maze_keys[i])

    def pick_tool_flags(self, tool):
        variant  = random.choice(self.conf['tool'][tool]['variant'])
        flags = ""
        if 'toggle' in self.conf['tool'][tool].keys():
            for opt in self.conf['tool'][tool]['toggle']:
                if random.randint(0,1) == 1:
                    flags += opt + ' '
        if 'choose' in self.conf['tool'][tool].keys():
            for flag, options in self.conf['tool'][tool]['choose'].items():
                chosen = random.choice(options)
                if chosen != 0:
                    flags += flag + chosen + ' '
        return variant,flags


    def generate_mazes(self):
        if self.conf['maze_gen'] == 'container':
            paramss = self.fetch_maze_params()
            LOGGER.info("Generating %d more mazes.", len(paramss))
            maze_gen.generate_mazes(paramss, get_temp_dir(),self.conf['workers'],self.conf['gen_time'])
            for params in paramss:
                self.mazes.update({maze: params for maze in maze_gen.get_maze_names(params)})
        else:
            params = get_random_params(self.conf)
            maze_gen.generate_maze(params, get_temp_dir(), get_minotaur_root())
            self.mazes.update({maze: params for maze in maze_gen.get_maze_names(params)})

    def fetch_maze_params(self):                                                                 
        return [get_random_params(self.conf) for _ in range(min(self.repeats,ceil(ceil(self.conf['workers']/len(self.conf['tool']))*self.conf['batch_size']/max(1,self.conf['transforms']))))] # NUMNB_BATCHES*SIZE / MAZES_PER_PARAMS

def fetch_works(conf: dict, gen: Target_Generator):
    new_targets = list(it.islice(gen, 0, conf['workers']*conf['batch_size']))
    return list(map(lambda w: w[1],new_targets)), list(map(lambda w : w[1], filter(lambda w: w[0], new_targets)))


def get_temp_dir():
   return os.path.join('/tmp','minotaur_mazes')

def get_maze_dir(maze=''):
    return os.path.join(get_temp_dir(),'src', maze)

def get_batch_file(batch: int):
    return get_maze_dir(docker.BATCH_FILE_FORMAT % batch)

def get_containers_needed(conf, works): 
    return min(ceil(len(works)/conf['batch_size']), conf['workers'])

def spawn_containers(conf, works):
    procs = []
    for i in range(get_containers_needed(conf,works)):
        target = works[i*conf['batch_size']]
        procs.append(docker.spawn_docker(conf['memory'], target.index, target.tool,get_maze_dir(),i,True))
    commands.wait_for_procs(procs)
    time.sleep(5)

def run_tools(conf: dict,works: 'list[Target]'):
    duration = conf['duration']
    procs = []
    for i in range(get_containers_needed(conf, works)):
        target  = works[i*conf['batch_size']]
        procs.append(docker.run_docker(duration, target.tool, target.index, target.variant, target.flags, target.index))
    commands.wait_for_procs(procs)
    time.sleep(3) 

def store_outputs(conf: dict, out_dir: str, works: list[Target]):
    has_bug = False
    procs = []
    for i in range(get_containers_needed(conf,works)):
        target = works[i*conf['batch_size']]
        procs.append(docker.collect_docker_results(target.tool, target.index, conf['expected_result']))
    commands.wait_for_procs(procs)
    time.sleep(5)

    for i in range(get_containers_needed(conf,works)):
        w = works[i*conf['batch_size']]
        out_path = os.path.join(out_dir, w.tool, str(w.index))
        os.system(f'mkdir -p {out_path}')
        docker.copy_docker_results(w.tool, w.index, out_path)
        docker.kill_docker(w.tool, w.index)
    time.sleep(5)


    for w in works:
        # Write file details into summary
        runtime = 'notFound'
        tag = 'notFound'
        out_path = os.path.join(out_dir, w.tool, str(w.index), w.maze)
        if os.path.isdir(out_path):
            for filename in os.listdir(out_path):
                if len(filename.split('_')) == 2:
                    runtime, tag = filename.split('_')
                    if (tag == 'fn'):
                        if conf['abort_on_error']:
                            has_bug = True
                        commands.run_cmd(CP_CMD % (get_maze_dir(w.maze), out_path)) # Keep buggy mazes
                    write_summary(conf, out_dir, w, tag, runtime)
        if runtime == 'notFound' or tag == 'notFound':
            write_summary(conf, out_dir, w, tag, runtime)
    return has_bug

def write_summary(conf,out_dir, target,tag,runtime):
    maze, tool, batch_id, params, variant, flags = target
    out_path = os.path.join(out_dir,tool, str(batch_id),maze)
    if (conf['verbosity'] == 'bug' or conf['verbosity'] == 'bug_only') and tag not in ('fp', 'fn'):
        commands.run_cmd(REMOVE_CMD % out_path)
        if conf['verbosity'] == 'bug_only':
            return
    offset = 0 if 'keepId' in params['t'] else 1
    with open(out_dir + '/summary.csv', 'a') as f:
        u = '0' if 'u' not in params.keys() else '1'
        f.write(tool + ',' + variant + ',' + flags + ',' + str(maze_gen.get_params_from_maze(maze)['m'] + offset) + ',' + u + ',') # TODO this is a liiiitle bit hacky
        for key, value in params.items():
            if key == 's':
                f.write(str(params['s'].split('/')[-1] + ','))
            elif key == 'u':
                continue # We already wrote u 
            elif key in conf['parameters'].keys():
                f.write(str(value) + ',')
        f.write(f'{runtime},{tag}')
        f.write('\n')
    if conf['verbosity'] == 'summary':
        commands.run_cmd(REMOVE_CMD % out_path)


def write_summary_header(conf, out_dir):
    with open(out_dir + '/summary.csv', 'w') as f:
        f.write('tool,variant,flags,id,u,')
        for key in conf['parameters'].keys():
            if key != 'u':
                f.write(str(key)+',')
        f.write('runtime,status\n')

def cleanup(completed: 'list[Target]'):
    procs = []
    while(len(completed) > 0):
        target = completed.pop()
        procs.append(commands.spawn_cmd(REMOVE_CMD % get_maze_dir(target.maze)))
        procs.append(commands.spawn_cmd(REMOVE_CMD % get_batch_file(target.index)))
    commands.wait_for_procs(procs)

def get_minotaur_root():
    mainfile = sys.modules['__main__'].__file__ # pylint: disable=no-member 
    return os.path.dirname(os.path.realpath('' if mainfile is None else mainfile))

def main(conf, out_dir):
    os.system(f'mkdir -p {out_dir}')
    if 'seed' in conf.keys():
        random.seed(conf['seed'])

    write_summary_header(conf, out_dir)
    done = False

    gen = Target_Generator(conf)
    while gen.has_targets() and not done: # -1 for inifinity
        works, to_remove = fetch_works(conf, gen)
        spawn_containers(conf, works)
        run_tools(conf, works)
        done = store_outputs(conf, out_dir, works)
        cleanup(to_remove)

    commands.run_cmd(REMOVE_CMD % get_temp_dir())

def load(argv):
    conf_path = os.path.join(get_minotaur_root(),'test',argv[0] + '.conf.json')
    out_dir = argv[1]
    conf = load_config(conf_path)
    main(conf, out_dir)
