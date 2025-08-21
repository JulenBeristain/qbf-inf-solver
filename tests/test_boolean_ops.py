# test_boolean_ops.py

##############################################################################################
### IMPORTS ##################################################################################

from copy import deepcopy
from typing import Dict
from src.regularize_tuples import regularize, RCNF

# Note: we only import the _tuples version because we need the pretty_print function to visualize
#   the results. In this file we only have basic cases to test visually if the boolean operations
#   work.

##############################################################################################
### TESTS ####################################################################################

def test_rcnf_conjunction(config: Dict[str, bool]) -> None:
    print("TEST C-CNF CONJUNCTION...")
    clauses_true = []
    clauses_false = [[]]
    clauses1 = [[1]]
    clauses2 = [[-2], [2,1], [-1]]
    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]

    tree1 = regularize(deepcopy(clauses_true), None, config)
    tree2 = regularize(deepcopy(clauses3), None, config)
    conj = RCNF.conjunction(tree1, tree2, config)
    assert conj == tree2, "No hemos conseguido conjunción con True"

    tree1 = regularize(deepcopy(clauses_false), None, config)
    #tree2 = regularize(deepcopy(clauses3), None, config)
    conj = RCNF.conjunction(tree1, tree2, config)
    assert conj == False, "No hemos conseguido conjunción con False"
    
    tree1 = regularize(deepcopy(clauses1), None, config)
    tree2 = regularize(deepcopy(clauses2), None, config)
    conj = RCNF.conjunction(tree1, tree2, config)
    RCNF.pretty_print(conj)

    tree1 = regularize(deepcopy(clauses2), None, config)
    tree2 = regularize(deepcopy(clauses3), None, config)
    conj = RCNF.conjunction(tree1, tree2, config)
    RCNF.pretty_print(conj)
    print('-' * 50)

def test_rcnf_disjunction(config: Dict[str, bool]) -> None:
    print("TEST C-CNF DISJUNCTION...")
    clauses_true = []
    clauses_false = [[]]
    clauses1 = [[1]]
    clauses2 = [[-2], [2,1], [-1]]
    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]

    tree1 = regularize(deepcopy(clauses_true), None, config)
    tree2 = regularize(deepcopy(clauses3), None, config)
    disj = RCNF.disjunction(tree1, tree2, config)
    assert disj == True, "No hemos conseguido disyunción con True"

    tree1 = regularize(deepcopy(clauses_false), None, config)
    #tree2 = regularize(deepcopy(clauses3), None, config)
    disj = RCNF.disjunction(tree1, tree2, config)
    assert disj is tree2, "No hemos conseguido disyunción con False"
    
    tree1 = regularize(deepcopy(clauses1), None, config)
    tree2 = regularize(deepcopy(clauses2), None, config)
    disj = RCNF.disjunction(tree1, tree2, config)
    RCNF.pretty_print(disj)

    tree1 = regularize(deepcopy(clauses2), None, config)
    tree2 = regularize(deepcopy(clauses3), None, config)
    disj = RCNF.disjunction(tree1, tree2, config)
    RCNF.pretty_print(disj)
    print('-' * 50)

##############################################################################################
### MAIN #####################################################################################

# Note: to be able to use the advanced version of the inf_solver, we need to define the 
#   configuration too.

if __name__ == '__main__':

    config = {
        'debugging'                         : False,    # No es una variante a experimentar. A False para no printear innecesariamente
        'pre_simplify_tautologies'          : True,     # Hacerlo siempre
        'iterative'                         : True,     # Hacerlo siempre (eliminate_variables y simplify)

        'conjunction_direct_association'    : True,
        
        'simplify'                          : True,    # Afecta a regularize, conjunction y disjunction
        
        'preprocessor'                      : False,    # TO AVOID THE NEED OF QUANTIFIERS WHEN CALLING TO regularize
        
        'cached_nodes'                      : True,    # Afecta a create_node -> regularize, simplify, conjunction, disjunction
        'equals_with_is'                    : False,     # Solo si cached is True
        
        'absorb_with_prefixes'              : False,
        'disable_gc'                        : True,
        'check_sat'                         : True,
    
        'conjunction_parallel'              : False,
        'conjunction_parallel_lazy'         : False,     # Solo aplicable si conjunction_parallel is True

        'disjunction_parallel'              : False,
        'disjunction_parallel_conjs'        : False,    # Solo aplicable si disjunction_parallel is True
        'disjunction_parallel_disjs'        : False,    # Solo aplicable si disjunction_parallel is True
        'disjunction_parallel_total'        : True,
        
        # Nota: la versión lru_cache no es compatible con config, por ser éste un dict no hasheable
        # conjunction_serial_basic | conjunction_serial (lru) | conjunction_serial_manual | conjunction_serial_manual_ids
        'f_conjunction_serial'              : RCNF.conjunction_serial_manual,
        # disjunction_serial_basic | disjunction_serial (lru) | disjunction_serial_manual | disjunction_serial_manual_ids
        'f_disjunction_serial'              : RCNF.disjunction_serial_manual,

        'version_cached'                    : False,
        'version_cached_cleanup'            : None,     # Estos solo son posibles de realizar si version_cached is True
        'version_cached_memo_lru'           : None,     # nocleanup OBLIGATORIAMENTE
        'version_cached_memo_dicts'         : None,    # Este podemos combinarlo con cleanup y nocleanup
    }

    assert not config['debugging'], "Incorrect configuration! [1]"
    assert config['pre_simplify_tautologies'], "Incorrect configuration! [2]"
    assert config['iterative'], "Incorrect configuration! [3]" 
    assert config['cached_nodes'] or not config['equals_with_is'], "Incorrect configuration! [5]"
    assert not config['equals_with_is'] or not config['conjunction_parallel'], "Incorrect configuration! [6]"
    assert not config['equals_with_is'] or not config['disjunction_parallel'], "Incorrect configuration! [7]"
    assert not config['disjunction_parallel'] or (config['disjunction_parallel_conjs'] or config['disjunction_parallel_disjs']), "Incorrect configuration! [8]"
    assert not config['disjunction_parallel'] or not config['disjunction_parallel_total'], "Incorrect configuration! [8.5]"
    assert not config['version_cached'], "Incorrect script (this is tuples) for set value cached version! [9]"

    
    possible_f_conj_serial = [RCNF.conjunction_serial_basic, RCNF.conjunction_serial, 
                              RCNF.conjunction_serial_manual, RCNF.conjunction_serial_manual_ids]
    assert config['f_conjunction_serial'] in possible_f_conj_serial, "Incorrect configuration! [11]"
    possible_f_disj_serial = [RCNF.disjunction_serial_basic, RCNF.disjunction_serial, 
                              RCNF.disjunction_serial_manual, RCNF.disjunction_serial_manual_ids]
    assert config['f_disjunction_serial'] in possible_f_disj_serial, "Incorrect configuration! [12]"
    
    assert config['cached_nodes'] or (config['f_conjunction_serial'] != RCNF.conjunction_serial_manual_ids), "Incorrect configuration! [13]"
    assert config['cached_nodes'] or (config['f_disjunction_serial'] != RCNF.disjunction_serial_manual_ids), "Incorrect configuration! [14]"


    test_rcnf_conjunction(config)
    test_rcnf_disjunction(config)
