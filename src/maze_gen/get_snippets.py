import os
from smt2.converter import get_array_helpers, get_bv_helpers
from smt2.z3_converter import ARRAY_SIZE_STRING
from storm.utils.randomness import Randomness
import smt2.z3_parser
import transforms

# Place where mutants will be generated #
MUTANT_LOC = '/tmp/minotaur-files'

def get_storm_snippets_from_file(file: str, seed: int, n: int, constraint_call: str = '__VERIFIER_assume', depth=10, conjuncts=10) \
    -> list[list[str]]:
    """
    Generate n mutants using storm and translate the corresponding assertions
    :param file: path to seed file
    :param seed: integer seed to control randomness
    :param n: number of mutants to generate
    :param constraint_call: wrap expression X in call(X);
    :param depth: Size of each assertion (~depth of formula tree)
    :param conjuncts: Size of each assertion (~depth of formula tree)
    :returns:
        List of assumptions per mutant.
        Every list of assumptions (in C) is guaranteed to be SAT. 
        Also every mutant is guaranteed to share the same model, so the conjunction of
        mutants should also be SAT.
    """
    t_dict = transforms.parse_transformations(f'storm{conjuncts}x{depth}_sat')
    os.system(f'mkdir -p {MUTANT_LOC}')
    snippets = []
    rand = Randomness(seed)
    while len(snippets) < n:
        os.system(f'mkdir -p {MUTANT_LOC}')
        mutants = transforms.run_storm(file, MUTANT_LOC, seed, n, t_dict)
        for mutant in mutants:
            try:
                snippets.extend(get_snippets_for_mutants(constraint_call, t_dict, [mutant]))
            except ValueError:
                print(f"Failed to convert mutant {mutant}")
    os.system(f'rm -r {MUTANT_LOC}')
    return snippets

def get_sat_snippets_from_file(file: str, seed: int, n: int, constraint_call: str = '__VERIFIER_assume', depth=20, conjuncts=10) \
    -> list[list[str]]:
    """
    Generate n mutants using mixed mode; filter SAT one  and translate the corresponding assertions
    :param file: path to seed file
    :param seed: integer seed to control randomness
    :param n: number of mutants to generate
    :param constraint_call: wrap expression X in call(X);
    :param depth: Size of each assertion (~depth of formula tree)
    :param conjuncts: Size of each assertion (~depth of formula tree)
    :returns:
        List of assumptions per mutant.
        Every list of assumptions (in C) is guaranteed to be SAT. 
        However different mutants might have different models.
        Might take longer, as we might generate a lot of UNSAT mutants.
        Also some mutants might fail to be translated, in which case we generate more.
    """
    t_dict = transforms.parse_transformations(f'fuzz{conjuncts}x{depth}_sat')
    snippets = []
    rand = Randomness(seed)
    while len(snippets) < n:
        os.system(f'mkdir -p {MUTANT_LOC}')
        mutants = [m for m in transforms.run_formula_builder(file, MUTANT_LOC, rand.get_random_integer(0,65000), n, t_dict) if 'unsat' not in m]
        for mutant in mutants:
            try:
                snippets.extend(get_snippets_for_mutants(constraint_call, t_dict, [mutant]))
            except ValueError:
                print(f"Failed to convert mutant {mutant}")
    os.system(f'rm -r {MUTANT_LOC}')
    return snippets

def get_random_snippets_from_file(file: str, seed: int, n: int, constraint_call: str = '__VERIFIER_assume', depth=20, conjuncts=10) \
    -> list[list[str]]:
    """
    Generate n mutants using mixed mode. 
    :param file: path to seed file
    :param seed: integer seed to control randomness
    :param n: number of mutants to generate
    :param constraint_call: wrap expression X in call(X);
    :param depth: Size of each assertion (~depth of formula tree)
    :param conjuncts: Size of each assertion (~depth of formula tree)
    :returns:
        List of assumptions per mutant.
        Assumptions might be sat or unsat.
        Some mutants might fail to be translated, in which case we generate more.
        Might therefore run a bit longer than STORM.
    """
    t_dict = transforms.parse_transformations(f'fuzz{conjuncts}x{depth}_sat')
    snippets = []
    rand = Randomness(seed)
    while len(snippets) < n:
        os.system(f'mkdir -p {MUTANT_LOC}')
        mutants = transforms.run_formula_builder(file, MUTANT_LOC, rand.get_random_integer(0,65000), n, t_dict)
        for mutant in mutants:
            try:
                snippets.extend(get_snippets_for_mutants(constraint_call, t_dict, [mutant]))
            except ValueError:
                print(f"Failed to convert mutant {mutant}")
    os.system(f'rm -r {MUTANT_LOC}')
    return snippets

def get_helpers_for_file(file: str) -> str:
    """
    Return the helper functions needed to translate a given file
    """
    logic = smt2.z3_parser.get_logic_from_file(file)
    helper_string = get_bv_helpers(True, logic)
    if 'A' in logic: ## Arrays
        lines = get_array_helpers(0).split('\n')
        # Remove the line defining array size
        array_helpers = '\n'.join(lines[0:3]+lines[4:])
        helper_string += array_helpers
    return helper_string


def get_snippets_for_mutants(constraint_call, t_dict, mutants):
    parse_results = [smt2.z3_parser.parse(mutant, t_dict, False, True) for mutant in mutants]
    snippets = []
    for (constraints, vars_to_types, array_size) in parse_results:
        arr_str = f"const int {ARRAY_SIZE_STRING} = {array_size};"        
        var_strs = [get_initialisation(var,vartype) for var, vartype in vars_to_types.items()]
        expressions_strings = [f"{constraint_call}({constraint});" for constraint in constraints]
        snippets.append([arr_str]+var_strs+expressions_strings)
    return snippets

def get_initialisation(var, var_type):
    if '[' in var: #Arrays
        return "{} {};".format(var_type.split('_')[-1],var)
    if var_type == 'bool':
        return "_Bool {} = __VERIFIER_nondet_bool();".format(var)
    if var_type == 'const bool':
        return " const _Bool {} = __VERIFIER_nondet_bool();".format(var)
    orig_type = var_type
    short_type = orig_type.split(" ")[-1]
    if 'unsigned' in orig_type:
        short_type = 'u' + short_type
    return "{} {} = __VERIFIER_nondet_{}();".format(var_type, var, short_type)


# Usage: python3 get_snippets.py /path/to/smt
if __name__ == '__main__':
    import sys
    print(get_helpers_for_file(sys.argv[1]))
    for snippet in get_storm_snippets_from_file(sys.argv[1], 0, 10,  depth=20, conjuncts=5):
        print('----------------')
        print('\n'.join(snippet))