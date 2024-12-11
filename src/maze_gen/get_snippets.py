import os
from smt2.z3_converter import ARRAY_SIZE_STRING
from storm.utils.randomness import Randomness
from smt2. 
import smt2.z3_parser
import transforms

MUTANT_LOC = '/tmp/minotaur-files'

def get_storm_snippets_from_file(file: str, seed: int, n: int, constraint_call: str = '__VERIFIER_assume', depth=10, conjuncts=20) \
    -> list[list[str]]:
    t_dict = transforms.parse_transformations('storm_sat')
    os.system(f'mkdir -p {MUTANT_LOC}')
    mutants = transforms.run_storm(file, MUTANT_LOC, seed, n, t_dict)
    snippets = get_snippets_for_mutants(constraint_call, t_dict, mutants)
    os.system(f'rm -r {MUTANT_LOC}')
    return snippets

def get_fb_snippets_from_file(file: str, seed: int, n: int, constraint_call: str = '__VERIFIER_assume', depth=10, conjuncts=20) \
    -> list[list[str]]:
    t_dict = transforms.parse_transformations('fuzz_sat')
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


def get_bv_helpers(well_defined=True, logic="QF_AUFBV") -> str:
    """Returns helper functions for BV translation
    :param well_defined: Also return helpers for well_definedness 
    """
    res = "\n\n//Helper functions for division and casts\n"
    res +=  """long scast_helper(unsigned long i, unsigned char width){
    if((i & (1ULL << (width-1))) > 0){
        return (long)(((((1ULL << (width-1)) - 1) << 1) + 1) - i) * (-1) - 1;
    }
    return i;\n}\n"""
    res += """unsigned long rotate_helper(unsigned long bv, unsigned long ammount, int left, int width){
    if(ammount == 0)
        return bv;
    if(left)
        return (bv << ammount) | (bv >> (width-ammount));
    return (bv >> ammount) | (bv << (width-ammount));\n}"""
    res += """unsigned long ashift_helper(unsigned long bv, unsigned long ammount, int width){
    if(ammount == 0)
        return bv;
    if (((1U << (width-1)) & bv) == 0) // positive ashr == lshr
        return bv >> ammount;
    return (((1 << ammount)-1) << (width - ammount)) | (bv >> ammount);\n}\n"""


    if well_defined and 'BV' in logic:
        res += """signed long sdiv_helper(long l, long r, int width){
    if(r == 0){
        if(l >= 0)
            return -1LL >> (64-width); // Make sure we shift with 0s
        return 1;
    } else if ((r == -1) && (l == ((-0x7FFFFFFFFFFFFFFFLL-1) >> (64-width))))
        return 0x8000000000000000ULL >> (64-width);
    return l / r;\n}"""
        res += """unsigned long div_helper(unsigned long l, unsigned long r, int width){
    if(r == 0)
        return -1ULL >> (64-width);
    return l / r;\n}"""
        res += """long srem_helper(long l, long r, int width){
    if(r == 0)
        return l;
    if ((r == -1) && (l == ((-0x7FFFFFFFFFFFFFFFLL-1) >> (64-width))))
        return 0;
    return l % r;\n}"""
        res += """unsigned long rem_helper(unsigned long l, unsigned long r, int width){
    if(r == 0)
        return l;
    return l % r;\n}\n"""
    elif well_defined:
        res += """signed long div_helper(long l, long r, int width){
    if(r == 0)
        return __VERIFIER_nondet_long();
    return l / r;\n}"""

    return res

def get_array_helpers(size):
    """Returns helper functions for Array translation
    :param size: Array size for the program
    """
    res = "\n\n//Array support\n"
    res += f"const int {ARRAY_SIZE_STRING} = {size};\n"
    res += """long* value_store(long* a,long pos,long v){
    a[pos] = v;
    return a;\n}\n"""
    res += """long* array_store(long* a,long pos,long* v, int size){
    for (int i=0;i<size;i++){
        a[pos*size+i] = v[i];
    }
    return a;\n}\n"""
    res += ("""int array_comp(long* a1, long* a2, int size){
    for(int i = 0; i < size; i++){
    \tif(a1[i] != a2[i]) return 0;
    }
    return 1;\n}\n""")
    res += ("""void init(long* array, int width,int size){
    unsigned long mask = (((1ULL << (width-1)) - 1) << 1) + 1;
    for(int i = 0; i < size; i++){
    \tarray[i] = scast_helper(mask & __VERIFIER_nondet_ulong(), width);
    }\n}""")
    return res


if __name__ == '__main__':
    for snippet in get_storm_snippets_from_file('/home/markus/MinotaurProject/bitvector/bitvector-s3_srvr_3_alt.BV.c.cil-test000045.smt2', 0, 10):
        print('----------------')
        print('\n'.join(snippet))
    
    print('\n'*5)
    
    for snippet in get_fb_snippets_from_file('/home/markus/MinotaurProject/bitvector/bitvector-s3_srvr_3_alt.BV.c.cil-test000045.smt2', 0, 10):
        print('----------------')
        print('\n'.join(snippet))