# test_regularize.py

##############################################################################################
### IMPORTS ##################################################################################

import os
from time import time
from sys import setrecursionlimit
from copy import deepcopy
from typing import Dict
from src.regularize_tuples import regularize, RCNF
from src.total_size import get_total_size
from src.qbf_parser import read_qdimacs_from_file_unchecked

# Note: we only import the _tuples version because we need the pretty_print function to visualize
#   the results. In this file we only have basic cases to test visually if regularize works.

#########################################################################################
### TESTS
#########################################################################################

def test_regularize(config: Dict[str, bool]) -> None:
    print("TEST COMPACTIFY...")
    clauses_true = []
    clauses_false = [[]]

    tree_true = regularize(deepcopy(clauses_true), None, config)
    assert tree_true is True, "No hemos conseguido el árbol true a partir de lista vacía!!!"
    tree_false = regularize(deepcopy(clauses_false), None, config)
    assert tree_false is False, "No hemos conseguido el árbol false a partir de cláusula vacía!!!"

    clauses1 = [[1]]
    tree = regularize(clauses1, None, config)
    RCNF.pretty_print(tree)

    clauses2 = [[-2], [2,1], [-1]]
    tree = regularize(clauses2, None, config)
    RCNF.pretty_print(tree)

    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    tree = regularize(clauses3, None, config)
    RCNF.pretty_print(tree)
    print('-' * 50)

def test_no_absortion_needed(config: Dict[str, bool]) -> None:
    print("TEST NO ABSORTION NEEDED...")
    clauses = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    clauses_copy = deepcopy(clauses)

    config['absorb_with_prefixes'] = True
    tree = regularize(clauses, None, config)
    config['absorb_with_prefixes'] = False
    tree_no_absortion = regularize(clauses_copy, None, config)
    
    assert tree == tree_no_absortion, "No hemos conseguido el mismo árbol sin absorción!!!"
    print("INDEED!")
    print('-' * 50)


def test_memory_sizes(config: Dict[str, bool]) -> None:
    test_dir = 'data/Test_works/'
    directory_sat = test_dir + "sat"
    instance1 = directory_sat + "/r_100_80_11.qdimacs"
    instance2 = directory_sat + "/b.q"

    # We could use preprocessor=True configuration and quantifiers instead of None

    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    print(f"Total size of {instance2}: {get_total_size(clauses)}")
    tree = regularize(clauses, None, config)
    print(f"Total size of the tree: {get_total_size(tree)}")
    print(f"Depth of the tree: {RCNF.depth(tree)}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {RCNF.max_nodes(tree)}")
    print(f"Actual number of nodes: {RCNF.nodes(tree)}")

    print("-" * 30)

    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    print(f"Total size of {instance2}: {get_total_size(clauses)}")
    tree = regularize(clauses, None, config)
    print(f"Total size of the tree: {get_total_size(tree)}")
    print(f"Depth of the tree: {RCNF.depth(tree)}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {RCNF.max_nodes(tree)}")
    print(f"Actual number of nodes: {RCNF.nodes(tree)}")

############################################################################################################################
### IMPROVED REGULARIZE ####################################################################################################

from collections import deque
from functools import cmp_to_key
from src.types_qbf import *
from src.cnf_preprocessor import (
    eliminate_tautological_clauses_ordered, 
    eliminate_tautological_variables_ordered,
    preprocess_ordered,
    cmp_clauses,
    absorb_with_prefixes
)

def regularize_with_deque(clauses: CNF_Formula, quantifiers: List[QBlock], config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Function that transforms the CNF matrix of a quantified formula to RCNF, as a ternary tree with a level for
    each variable in the CNF. Although, as we store the variables in the nodes, we might have several variables
    in a level if some subformulas don't contain the variable corresponding to a given level. That way, we can 
    avoid having a complete ternary tree, which would need an exponential number of nodes.

    Args:
        clauses (CNF_Formula): the list of lists of ints that represents the matrix of the prenex quantified formula to be transformed to RCNF.
        quantifiers (List[QBlock]): the quantifiers of the complete formula. Used in the preprocessing of prenex quantified formulas' matrices.
        config (Dict[str, bool]): the configuration of the algorithm (in this case, used to decide if we simplify the formulas that we obtain).
        
    Returns:
        Tuple | bool: the ternary tree that represents the RCNF which is equivalent to the CNF formula in clauses.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    if config['pre_simplify_tautologies']:
        # set_trace()
        eliminate_tautological_clauses_ordered(clauses)
        eliminate_tautological_variables_ordered(clauses)

    if config['preprocessor']:
        # In place modification to clauses
        if preprocess_ordered(clauses, quantifiers) is False:
            return False
        
    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(cmp_clauses))

    # Third: we use associativity and absortion to remove clauses that have other clause(s) (the preceeding one do to the
    # previous sorting) as prefix(es)
    if config['absorb_with_prefixes']:
        absorb_with_prefixes(clauses)
        # Note: the previous step is not strictly necessary. We would reach a point were the empty list would
        # be found as the base case in _regularize, and we would obtain a totally equivalent answer.

    for i, c in enumerate(clauses):
        clauses[i] = deque(c)

    return _regularize_with_deque(clauses, config)
    

def _regularize_with_deque(clauses: CNF_Formula, config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Auxiliar recursive function for regularize.

    Precondition: there are no repeated variables in any clause, and clauses are already ordered as desired:
        1. Each clause is ordered by the absolute value of its literals.
        2. Clauses are ordered following the lexicographic order, considering also that -v < v.
    """
    
    # Si cláusulas vacías, entonces tenemos el literal True (elemento neutro de la conjunción)
    num_clauses = len(clauses)
    if num_clauses == 0:
        return True
    
    # Si contiene la cláusula vacía, entonces tenemos el literal False (elemento neutro de disyunción y dominante de conjunción)
    # Además, por la forma en la que hemos ordenado las cláusulas, la cláusula vacía vendrá al principio en todo caso. Por lo que 
    # es suficiente mirar la primera cláusula; el coste de esta comprobación es O(1). Y como último detalle, solo habrá una cláusula
    # vacía en todo caso, por haber absorbido los prefijos y las cláusulas idénticas.
    if len(clauses[0]) == 0:
        return False

    vn = abs(clauses[0][0])

    # Si algún phi_n == [] -> tree == True (mirar el primer caso base)
    # Si [] in phi_n       -> tree == False (mirar el segundo caso base)
    #   Además, gracias a haber eliminado los prefijos, sabemos que en este caso phi_n = [[]].
    #   Pero démonos cuenta de que no es estrictamente necesario. Con saber que [] in clauses
    #   ya estamos en el caso base, y además [] será el primer elemento. Por ello, añado el 
    #   parámetro que hace opcional el paso de absorción mediante prefijos.
    i = 0
    phi1 = []
    while i < num_clauses and clauses[i][0] == -vn:
        clause = clauses[i]
        clause.popleft()
        phi1.append(clause)
        i += 1
    phi2 = []
    while i < num_clauses and clauses[i][0] == vn:
        clause = clauses[i]
        clause.popleft()
        phi2.append(clause)
        i += 1
    phi3 = []
    while i < num_clauses:
        phi3.append(clauses[i])
        i += 1

    absTree = _regularize_with_deque(phi3, config)
    if absTree is False:
        return False
    negTree = _regularize_with_deque(phi1, config)
    posTree = _regularize_with_deque(phi2, config)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o Tuple
    
    phi = RCNF.create_node(vn, negTree, posTree, absTree, config)
    if config['simplify']:
        return RCNF.simplify_rcnf(phi, config)
    else:
        return phi


def regularize_with_index(clauses: CNF_Formula, quantifiers: List[QBlock], config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Function that transforms the CNF matrix of a quantified formula to RCNF, as a ternary tree with a level for
    each variable in the CNF. Although, as we store the variables in the nodes, we might have several variables
    in a level if some subformulas don't contain the variable corresponding to a given level. That way, we can 
    avoid having a complete ternary tree, which would need an exponential number of nodes.

    Args:
        clauses (CNF_Formula): the list of lists of ints that represents the matrix of the prenex quantified formula to be transformed to RCNF.
        quantifiers (List[QBlock]): the quantifiers of the complete formula. Used in the preprocessing of prenex quantified formulas' matrices.
        config (Dict[str, bool]): the configuration of the algorithm (in this case, used to decide if we simplify the formulas that we obtain).
        
    Returns:
        Tuple | bool: the ternary tree that represents the RCNF which is equivalent to the CNF formula in clauses.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    if config['pre_simplify_tautologies']:
        # set_trace()
        eliminate_tautological_clauses_ordered(clauses)
        eliminate_tautological_variables_ordered(clauses)

    if config['preprocessor']:
        # In place modification to clauses
        if preprocess_ordered(clauses, quantifiers) is False:
            return False
        
    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(cmp_clauses))

    # Third: we use associativity and absortion to remove clauses that have other clause(s) (the preceeding one do to the
    # previous sorting) as prefix(es)
    if config['absorb_with_prefixes']:
        absorb_with_prefixes(clauses)
        # Note: the previous step is not strictly necessary. We would reach a point were the empty list would
        # be found as the base case in _regularize, and we would obtain a totally equivalent answer.

    return _regularize_with_index(clauses, 0, config)
    

def _regularize_with_index(clauses: CNF_Formula, var_i: int, config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Auxiliar recursive function for regularize.

    Precondition: there are no repeated variables in any clause, and clauses are already ordered as desired:
        1. Each clause is ordered by the absolute value of its literals.
        2. Clauses are ordered following the lexicographic order, considering also that -v < v.
    """
    
    # Si cláusulas vacías, entonces tenemos el literal True (elemento neutro de la conjunción)
    num_clauses = len(clauses)
    if num_clauses == 0:
        return True
    
    # Si contiene la cláusula vacía, entonces tenemos el literal False (elemento neutro de disyunción y dominante de conjunción)
    # Además, por la forma en la que hemos ordenado las cláusulas, la cláusula vacía vendrá al principio en todo caso. Por lo que 
    # es suficiente mirar la primera cláusula; el coste de esta comprobación es O(1). Y como último detalle, solo habrá una cláusula
    # vacía en todo caso, por haber absorbido los prefijos y las cláusulas idénticas.
    if len(clauses[0]) <= var_i:
        return False

    vn = abs(clauses[0][var_i])

    # Si algún phi_n == [] -> tree == True (mirar el primer caso base)
    # Si [] in phi_n       -> tree == False (mirar el segundo caso base)
    #   Además, gracias a haber eliminado los prefijos, sabemos que en este caso phi_n = [[]].
    #   Pero démonos cuenta de que no es estrictamente necesario. Con saber que [] in clauses
    #   ya estamos en el caso base, y además [] será el primer elemento. Por ello, añado el 
    #   parámetro que hace opcional el paso de absorción mediante prefijos.
    i = 0
    phi1 = []
    while i < num_clauses and clauses[i][var_i] == -vn:
        phi1.append(clauses[i])
        i += 1
    phi2 = []
    while i < num_clauses and clauses[i][var_i] == vn:
        phi2.append(clauses[i])
        i += 1
    phi3 = []
    while i < num_clauses:
        phi3.append(clauses[i])
        i += 1

    absTree = _regularize_with_index(phi3, var_i, config)
    if absTree is False:
        return False
    negTree = _regularize_with_index(phi1, var_i + 1, config)
    posTree = _regularize_with_index(phi2, var_i + 1, config)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o Tuple
    
    phi = RCNF.create_node(vn, negTree, posTree, absTree, config)
    if config['simplify']:
        return RCNF.simplify_rcnf(phi, config)
    else:
        return phi

############################################################################################################################
############################################################################################################################


def test_big_instance_regularization_times(config: Dict[str, bool]) -> None:
    instances = [
        '134.s713_d4_s.qdimacs',
        '154.stmt27_149_224.qdimacs.txt',
        '23.biu.qdimacs',
        '50.c3_BMC_p1_k256.qdimacs'
    ]
    dir = 'data/integration-tests'
    paths = [os.path.join(dir, inst) for inst in instances]

    # In this case we can access to quantifiers
    config['preprocessor'] = True

    setrecursionlimit(5000)

    for inst, path in zip(instances, paths):
        print("-" * 30)
        print(inst)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(path)
        print(f"Total size: {get_total_size(clauses)}")
        t0 = time()
        #tree = regularize(clauses, quantifiers, config)
        #tree = regularize_with_deque(clauses, quantifiers, config)
        tree = regularize_with_index(clauses, quantifiers, config)
        t1 = time()
        print(f"Total size of the tree: {get_total_size(tree)}")
        print(f"Depth of the tree: {RCNF.depth(tree)}")
        print(f'Number of variables: {nv}')
        print(f"Max number of nodes: {RCNF.max_nodes(tree)}")
        print(f"Actual number of nodes: {RCNF.nodes(tree)}")
        print(f"REGULARIZATION TIME = {t1 - t0: .2f} s")
    print("-" * 30)


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


    #test_regularize(config)
    #test_no_absortion_needed(config)
    #test_memory_sizes(config)
    test_big_instance_regularization_times(config)