# regularize_final.py

##############################################################################################
### IMPORTS ##################################################################################

from functools import cmp_to_key, lru_cache
from pdb import set_trace
from .types_qbf import *

##############################################################################################
### BOOLEAN OPERATIONS AND FORMULA SIMPLIFICATIONS WITH RCNFs ################################

##########################################################################################
### NODE CREATION ########################################################################


@lru_cache(maxsize=None)
def create_node(v: PositiveInt, negTree: Union[Tuple, bool], posTree: Union[Tuple, bool], absTree: Union[Tuple, bool]) -> Tuple:
    """
    Function to create nodes and cache them in a lru_cache, so no formula is repeated in memory.

    Args:
        v (PositiveInt): the variable of the node (the one of the root node for the current subformula).
        negTree (Tuple | bool): the node that is the root of the first subtree, which is the subformula that contains ¬v, or True/False if there is none.
        posTree (Tuple | bool): same as negTree, but for the second subtree, the subformula that contains +v.
        absTree (Tuple | bool): same as negTree, but for the third subtree, the subformula that doesn't contain v.
        
    Returns:
        Tuple: the created new node, a 4-tuple with the main arguments.
    """
    return (v, negTree, posTree, absTree)

##########################################################################################
### CLEAN CACHES #########################################################################

def clean_caches() -> None:
    """
    Function to clean the caches of the nodes and the memoization caches of the boolean operations.
    """
    create_node.cache_clear()
    conjunction_cache.clear()
    disjunction_cache.clear()

###########################################################################################
### CONJUNCTION ###########################################################################

conjunction_cache: Dict[Tuple[Tuple, Tuple], Union[Tuple, bool]] = {}

def conjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool]) -> Union[Tuple, bool]:
    """
    Function that calculates the conjunction between two RCNF formulas. The final version corresponds
    to the serial version that memoizes results manually in a dict, alongside other most efficient
    configurations.

    Args:
        tree1 (Tuple | bool): the first formula to perform the conjunction.
        tree2 (Tuple | bool): the second formula to perform the conjunction.
        
    Returns:
        Tuple | bool: the RCNF formula equivalent to the conjunction of tree1 and tree2.
    """
    ## Base cases
    # Identity (true is the neutral element of conjunction)
    if tree1 is True: return tree2
    if tree2 is True: return tree1

    # Domination (false is the dominant element of conjunction)
    if tree1 is False or tree2 is False: 
        return False

    # Commutativity
    if tree1[0] < tree2[0]:
        tree1, tree2 = tree2, tree1

    res = conjunction_cache.get((tree1, tree2))
    if res is not None:
        return res

    ## Recursive cases
    # Same maximum variable in the root
    if tree1[0] == tree2[0]:
        conj_abs = conjunction(tree1[3], tree2[3])
        if conj_abs is False:
            conjunction_cache[(tree1, tree2)] = False
            return False
        conj_neg = conjunction(tree1[1], tree2[1])
        conj_pos = conjunction(tree1[2], tree2[2])
        if conj_neg is False and conj_pos is False:
            conjunction_cache[(tree1, tree2)] = False
            return False
        if conj_neg is True and conj_pos is True:
            conjunction_cache[(tree1, tree2)] = conj_abs
            return conj_abs # Ya sea True o Tuple
        
        phi = create_node(tree1[0], conj_neg, conj_pos, conj_abs)
        res = simplify_rcnf(phi)
        conjunction_cache[(tree1, tree2)] = res
        return res
        
    # Different maximum variables, where tree1[0] > tree2[0]
    conj_abs = conjunction(tree1[3], tree2)
    if conj_abs is False:
        conjunction_cache[(tree1, tree2)] = False
        return False

    phi = create_node(tree1[0], tree1[1], tree1[2], conj_abs)
    res = simplify_rcnf(phi)
    conjunction_cache[(tree1, tree2)] = res
    return res
    
###########################################################################################
### DISJUNCTION ###########################################################################


disjunction_cache: Dict[Tuple[Tuple, Tuple], Union[Tuple, bool]] = {}

def disjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool]) -> Union[Tuple, bool]:
    """
    Function that calculates the disjunction between two RCNF formulas. The final version corresponds
    to the serial version that memoizes results manually in a dict, alongside other most efficient
    configurations.

    Args:
        tree1 (Tuple | bool): the first formula to perform the disjunction.
        tree2 (Tuple | bool): the second formula to perform the disjunction.
    
    Returns:
        Tuple | bool: the RCNF formula equivalent to the disjunction of tree1 and tree2.
    """
    ## Base cases
    # Identity (false is the neutral element of disjunction)
    if tree1 is False: return tree2
    if tree2 is False: return tree1

    # Domination (true is the dominant element of disjunction)
    if tree1 is True or tree2 is True:
        return True

    # Commutativity
    if tree1[0] < tree2[0]:
        tree1, tree2 = tree2, tree1

    res = disjunction_cache.get((tree1, tree2))
    if res is not None:
        return res

    ## Recursive cases
    # Same maximum variable in the root
    if tree1[0] == tree2[0]:
        phi_3_ = disjunction(tree1[3], tree2[3])
        if phi_3_ is False:
            disjunction_cache[(tree1, tree2)] = False
            return False
        
        phi_11_ = conjunction(tree2[1], tree2[3])
        phi_21_ = conjunction(tree2[2], tree2[3])
        
        phi_12_ = disjunction(tree1[1], phi_11_)
        phi_13_ = disjunction(tree1[3], tree2[1])
        phi_22_ = disjunction(tree1[2], phi_21_)
        phi_23_ = disjunction(tree1[3], tree2[2])

        phi_14_ = conjunction(phi_12_, phi_13_)
        phi_24_ = conjunction(phi_22_, phi_23_)
        if phi_14_ is False and phi_24_ is False:
            disjunction_cache[(tree1, tree2)] = False
            return False
        if phi_14_ is True and phi_24_ is True:
            disjunction_cache[(tree1, tree2)] = phi_3_
            return phi_3_ # Ya sea True o Tuple
        
        phi = create_node(tree1[0], phi_14_, phi_24_, phi_3_)
        res = simplify_rcnf(phi)
        disjunction_cache[(tree1, tree2)] = res
        return res
        
        
    # tree1[0] > tree2[0]
    disj_abs = disjunction(tree1[3], tree2)
    if disj_abs is False:
        disjunction_cache[(tree1, tree2)] = False
        return False
    disj_neg = disjunction(tree1[1], tree2)
    disj_pos = disjunction(tree1[2], tree2)
    if disj_neg is False and disj_pos is False:
        disjunction_cache[(tree1, tree2)] = False
        return False
    if disj_neg is True and disj_pos is True:
        disjunction_cache[(tree1, tree2)] = disj_abs
        return disj_abs # Ya sea True o Tuple
    
    phi = create_node(tree1[0], disj_neg, disj_pos, disj_abs)
    res = simplify_rcnf(phi)
    disjunction_cache[(tree1, tree2)] = res
    return res

###########################################################################################
### RCNF SIMPLIFICATION ###########################################################################

def simplify_rcnf(tree: Union[Tuple, bool]) -> Union[Tuple, bool]:
    """
    Function that calculates the simplification of the RCNF formula represented by tree. The final version
    is the iterative one. Remember the operations that are performed:

    1. If the first two subformulas are equal, the formula is equivalent to the conjunction between that and the third subformula.
        Properties: (inverse) distributivity, tautology, and True is the neutral element of conjunction
    2. If the first and third subformulas are equal, the first subformula can be replaced with True.
        Properties: absorbtion, True is the dominant element of disyunction, and then True is the neutral element of conjunction.
    3. Same as the 2, but with the second and third subformulas.

    They are performed continuosly until no one of them is applicable again.

    Args:
        tree (Tuple | bool): the formula to be simplified.
    
    Returns:
        Tuple | bool: the simplified RCNF formula equivalent to the formula represented by tree.
    """
    while True:
        # Necessary check if in the next case it is true and conjunction returns a boolean
        if tree is True or tree is False:
            return tree

        if tree[1] is tree[2]: # not == thanks to the caching of nodes. The same in the next tests
            tree = conjunction(tree[1], tree[3])
            continue
        
        # First condition to avoid infinite iteration when phi_1 = phi_3 = True
        if (tree[1] is not True) and (tree[1] is tree[3]):
            tree = create_node(tree[0], True, tree[2], tree[3])
            continue

        # First condition to avoid infinite iteration when phi_2 = phi_3 = True
        if (tree[2] is not True) and (tree[2] is tree[3]):
            tree = create_node(tree[0], tree[1], True, tree[3])
            continue
        
        return tree

#########################################################################################
### TRANSFORMATION FROM CNF -> RCNF #####################################################

from .cnf_preprocessor import (
    eliminate_tautological_clauses_ordered,
    eliminate_tautological_variables_ordered,
    preprocess_ordered, 
    cmp_clauses
) 

def regularize(clauses: CNF_Formula, quantifiers: List[QBlock]) -> Union[Tuple, bool]:
    """
    Function that transforms the CNF matrix of a quantified formula to RCNF, as a ternary tree with a level for
    each variable in the CNF. Although, as we store the variables in the nodes, we might have several variables
    in a level if some subformulas don't contain the variable corresponding to a given level. That way, we can 
    avoid having a complete ternary tree, which would need an exponential number of nodes.

    In the final version, the overhead of checking the configuration is eliminated, and we directly call to the 
    most efficient operations directly.

    Args:
        clauses (CNF_Formula): the list of lists of ints that represents the matrix of the prenex quantified formula to be transformed to RCNF.
        quantifiers (List[QBlock]): the quantifiers of the complete formula. Used in the preprocessing of prenex quantified formulas' matrices.
    
    Returns:
        Tuple | bool: the ternary tree that represents the RCNF which is equivalent to the CNF formula in clauses.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    eliminate_tautological_clauses_ordered(clauses)
    eliminate_tautological_variables_ordered(clauses)

    # In place modification to clauses
    if preprocess_ordered(clauses, quantifiers) is False:
        return False
        
    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(cmp_clauses))

    return _regularize(clauses)
    

def _regularize(clauses: CNF_Formula) -> Union[Tuple, bool]:
    """
    Auxiliar recursive function for regularize.

    Precondition: there are no repeated variables in any clause, and clauses are already ordered as desired:
        1. Each clause is ordered by the absolute value of its literals.
        2. Clauses are ordered following the lexicographic order, considering also that -v < v.
    
    Note: see test_regularization for a slightly more optimized version that avoids pop(0) operations with lists
        using an extra index for variables keeping the clauses intact. This version is left here for documentation
        purposes, because it is the one that has been used to do the measurements.
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
        clause.pop(0)
        phi1.append(clause)
        i += 1
    phi2 = []
    while i < num_clauses and clauses[i][0] == vn:
        clause = clauses[i]
        clause.pop(0)
        phi2.append(clause)
        i += 1
    phi3 = []
    while i < num_clauses:
        phi3.append(clauses[i])
        i += 1

    absTree = _regularize(phi3)
    if absTree is False:
        return False
    negTree = _regularize(phi1)
    posTree = _regularize(phi2)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o Tuple
    
    phi = create_node(vn, negTree, posTree, absTree)
    return simplify_rcnf(phi)

