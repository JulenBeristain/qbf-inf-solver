# compactify.py

#from __future__ import annotations # To use type hints of a class within the same class (alternative: string annotation)
from functools import cmp_to_key
from pdb import set_trace
from copy import deepcopy
from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
#from memory import get_total_size
from sys import getsizeof
from functools import lru_cache
from multiprocessing import Pool
from os import cpu_count
from concurrent.futures import ProcessPoolExecutor, as_completed

##############################################################################################
### COMPACTIFY ###############################################################################

class CCNF:
    """
    Class that contains only static methods to work with nested 4-tuples (id + ternary tree)
    that represent formulas in the CCNF form.

    TODO: a microoptimization would be to delete this class altogether and define all the following
        static methods as free functions.
    """
    
    ###################################
    ### COUNT NODE CREATION
    # NOTA: Detalle clave para esta implementación: bool es subtipo de int, por lo que True y 1 no se diferencian
    #       al usarse como claves de dicts. Por ello, empezamos con los IDs a partir de 2 (mirar en create_node que
    #       este valor inicial de 1 no se tiene en cuenta).
    _next_id = 1

    def num_nodes_created():
        return CCNF._next_id - 1
    
    def restart_node_counter():
        CCNF._next_id = 1
    ###################################

    tuple2id = {}
    id2tuple = {}

    def reset_nodes() -> None:
        CCNF.tuple2id = {}
        CCNF.id2tuple = {}
        CCNF._next_id = 1

    def create_node(v: PositiveInt, negTree: int | bool, posTree: int | bool, absTree: int | bool, cached = True) -> int:
        assert absTree is not False, \
        f"Variable [{v}]: se incumple ψ3 /= false !!!"
        assert (negTree is not False) or (posTree is not False), \
            f"Variable [{v}]: se incumple ψ1 /= false or ψ2 /= false !!!"
        assert (absTree is not True) or (posTree is not True) or (negTree is not True), \
            f"Variable [{v}]: se incumple ψ1 /= true or ψ2 /= true or ψ3 /= true !!!"
        
        assert isinstance(v, int) and v > 0, f"v={v} no es un entero positivo!!! (next_id={CCNF._next_id})"
        assert isinstance(negTree, int) or isinstance(negTree, bool), f"negTree={negTree} no es int o bool!!! (next_id={CCNF._next_id})"
        assert isinstance(posTree, int) or isinstance(posTree, bool), f"posTree={posTree} no es int o bool!!! (next_id={CCNF._next_id})"
        assert isinstance(absTree, int) or isinstance(absTree, bool), f"absTree={absTree} no es int o bool!!! (next_id={CCNF._next_id})"

        node = (v, negTree, posTree, absTree)
        node_id = CCNF.tuple2id.get(node)
        if node_id is None:
            CCNF._next_id += 1
            CCNF.tuple2id[node] = CCNF._next_id
            CCNF.id2tuple[CCNF._next_id] = node
            return CCNF._next_id
        return node_id

    def equals(tree1: int | bool, tree2: int | bool, cached = False) -> bool:
        """
        TODO: A mirooptmization would to be delete this function altogether.
        """
        return tree1 == tree2

    #######################
    # BOOLEAN OPERATIONS
    #######################

    # Variable estática para debuguear
    conjunction_calls = 0
    def reset_conjunction_calls() -> None:
        CCNF.conjunction_calls = 0

    def conjunction(id1: int | bool, id2: int | bool, 
                    cached: bool = True,
                    use_direct_association = True,
                    simplify = False,
                    parallel = False) -> int | bool:
        """
        Returns the conjunction between two C-CNF formulas.
        """
        CCNF.conjunction_calls += 1
        
        assert isinstance(id1, int) or isinstance(id1, bool), f"id1={id1} no es un ID de un nodo o un booleano!!!"
        assert isinstance(id2, int) or isinstance(id2, bool), f"id2={id2} no es un ID de un nodo o un booleano!!!"

        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if id1 is True: return id2
        if id2 is True: return id1

        # Domination (false is the dominant element of conjunction)
        if id1 is False or id2 is False: 
            return False

        tree1, tree2 = CCNF.id2tuple[id1], CCNF.id2tuple[id2]

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = CCNF.conjunction(tree1[3], tree2[3], simplify=simplify)
            if conj_abs is False:
                return False
            conj_neg = CCNF.conjunction(tree1[1], tree2[1], simplify=simplify)
            conj_pos = CCNF.conjunction(tree1[2], tree2[2], simplify=simplify)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = CCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if simplify:
                return CCNF.simplify_ccnf(phi)
            else:
                return phi

        # Different maximum variables
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1

        conj_abs = CCNF.conjunction(tree1[3], id2, simplify=simplify)
        if conj_abs is False:
            return False

        if use_direct_association:
            phi = CCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs)
            if simplify:
                return CCNF.simplify_ccnf(phi)
            else:
                return phi
        else:
            conj_neg = CCNF.conjunction(tree1[1], id2, simplify=simplify)
            conj_pos = CCNF.conjunction(tree1[2], id2, simplify=simplify)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = CCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if simplify:
                return CCNF.simplify_ccnf(phi)
            else:
                return phi

    def disjunction(id1: int | bool, id2: int | bool,
                    cached: bool = True, simplify = False, parallel = False) -> int | bool:
        """
        Returns the disjunction between two C-CNF formulas.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if id1 is False: return id2
        if id2 is False: return id1

        # Domination (true is the dominant element of disjunction)
        if id1 is True or id2 is True:
            return True

        tree1, tree2 = CCNF.id2tuple[id1], CCNF.id2tuple[id2]

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = CCNF.disjunction(tree1[3], tree2[3], simplify=simplify)
            if phi_3_ is False:
                return False
            
            phi_11_ = CCNF.conjunction(tree2[1], tree2[3], simplify=simplify)
            phi_21_ = CCNF.conjunction(tree2[2], tree2[3], simplify=simplify)
            
            phi_12_ = CCNF.disjunction(tree1[1], phi_11_, simplify=simplify)
            phi_13_ = CCNF.disjunction(tree1[3], tree2[1], simplify=simplify)
            phi_22_ = CCNF.disjunction(tree1[2], phi_21_, simplify=simplify)
            phi_23_ = CCNF.disjunction(tree1[3], tree2[2], simplify=simplify)

            phi_14_ = CCNF.conjunction(phi_12_, phi_13_, simplify=simplify)
            phi_24_ = CCNF.conjunction(phi_22_, phi_23_, simplify=simplify)
            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o int
            
            phi = CCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_)
            if simplify:
                return CCNF.simplify_ccnf(phi)
            else:
                return phi
            
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1
        
        disj_abs = CCNF.disjunction(tree1[3], id2, simplify=simplify)
        if disj_abs is False:
            return False
        disj_neg = CCNF.disjunction(tree1[1], id2, simplify=simplify)
        disj_pos = CCNF.disjunction(tree1[2], id2, simplify=simplify)
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o int
        
        phi = CCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs)
        if simplify:
            return CCNF.simplify_ccnf(phi)
        else:
            return phi

    def simplify_ccnf(tree: int | bool, cached: bool = True, iterative = True) -> int | bool:
        if iterative:
            return CCNF.simplify_ccnf_it(tree)
        return CCNF.simplify_ccnf_rec(tree)

    def simplify_ccnf_rec(id: int | bool, cached: bool = True) -> int | bool:
        #set_trace()
        # Necessary check if in the next case it is true and conjunction returns a boolean
        if id is True or id is False:
            return id

        tree = CCNF.id2tuple[id]

        if CCNF.equals(tree[1], tree[2]):
            phi = CCNF.conjunction(tree[1], tree[3], simplify=False)
            return CCNF.simplify_ccnf_rec(phi)

        # First condition to avoid infinite reqursion when phi_1 = phi_3 = True
        if tree[1] is not True and CCNF.equals(tree[1], tree[3]):
            phi = CCNF.create_node(tree[0], True, tree[2], tree[3])
            return CCNF.simplify_ccnf_rec(phi)

        # First condition to avoid infinite reqursion when phi_2 = phi_3 = True
        if tree[2] is not True and CCNF.equals(tree[2], tree[3]):
            phi = CCNF.create_node(tree[0], tree[1], True, tree[3])
            return CCNF.simplify_ccnf_rec(phi)
        
        return id

    def simplify_ccnf_it(id: int | bool, cached: bool = True) -> int | bool:
        while True:
            # Necessary check if in the next case it is true and conjunction returns a boolean
            if id is True or id is False:
                return id

            tree = CCNF.id2tuple[id]

            if CCNF.equals(tree[1], tree[2]):
                id = CCNF.conjunction(tree[1], tree[3], simplify=False)
                continue

            # First condition to avoid infinite iteration when phi_1 = phi_3 = True
            if tree[1] is not True and CCNF.equals(tree[1], tree[3]):
                id = CCNF.create_node(tree[0], True, tree[2], tree[3])
                continue

            # First condition to avoid infinite iteration when phi_2 = phi_3 = True
            if tree[2] is not True and CCNF.equals(tree[2], tree[3]):
                id = CCNF.create_node(tree[0], tree[1], True, tree[3])
                continue
            
            return id

    ###
    # MEMORY TROUBLE-SHOOTING
    ###
    def size(tree: int | bool, seen = None) -> int:
        if seen is None:
            seen = set()
        tree_id = id(tree)
        if tree_id in seen:
            return 0  # Ya contamos este objeto
        seen.add(tree_id)

        if tree is True or tree is False:
            return getsizeof(tree)
        tree_tuple = CCNF.id2tuple[tree]
        v, neg, pos, abs = tree
        return 2*(getsizeof(tree)+get_total_size(tree_tuple)) + CCNF.size(neg, seen) + CCNF.size(pos, seen) + CCNF.size(abs, seen)


#########################################################################################
#########################################################################################

def _cmp_clauses(clause1: Clause, clause2: Clause) -> int:
    """
    PRE: the literals in the clauses are ordered by their absolute values, in descending order (biggest to smallest).
         If v is in a clause, -v is not.

    1. Variables (absolute values of literals) are ordered in descending order, since we start looking for the greatest one.
    2. If variables are equal, the negative literal preceeds the positive one.
    3. If even the literals are equal, the comparison proceeds based on the next literal of both clauses.
    4. If a clause is a prefix of the other clause, the prefix (the shortest) preceeds the longest one.

    In the case of the prefix, it is not important that the prefix comes before or after the complete one. In the next phase,
    all complete clauses are going to be removed taking advantage of associativity and absortion, to avoid reaching a point
    in the recursion where phi_3' (the subformula that doesn't contain the variable in the next level of the tree) is false.
    It is not important but the choice has to be taken into account in the next fase. In fact, it is slightly more
    efficient to give more precedence to the prefix (as we do). That way, we will iterate reversely the list of clauses
    comparing each clause to its preceding one. If the preceding is a prefix, the current clause is deleted. As the longest clause
    is deleted and it was put closer to the end, the pop operation will have to copy leftwards one clause less.
    
    Another advantage (the real one) of giving more precedence to prefixes is that empty clauses (prefix of any other clause)
    will appear in the beginning, so it will be easy to check if we have the False literal.
    """
    len1, len2 = len(clause1), len(clause2)
    min_len = min(len1, len2)
    for i in range(min_len):
        l1, l2 = clause1[i], clause2[i]
        v1, v2 = abs(l1), abs(l2)
        if v1 < v2: return 1
        if v1 > v2: return -1
        # v1 == v2
        if l1 < l2: return -1
        if l1 > l2: return 1
        # l1 = l2 -> continue
    if len1 == len2: return 0
    if min_len == len1: return -1
    # min_len == len2
    return 1

def _is_prefix(prefix: List[int], complete: List[int]) -> bool:
    len_prefix = len(prefix)
    if len_prefix > len(complete):
        return False
    
    for i in range(len_prefix):
        if prefix[i] != complete[i]:
            return False
    
    return True


def _absorb_with_prefixes(clauses: CNF_Formula) -> int:
    """
    PRE: prefixes come before the complete one.

    Note: idempotence is a concrete case of absortion.
    """
    num = 0
    i = len(clauses) - 1
    while i > 0:
        complete = clauses[i]
        prefix = clauses[i-1]
        if _is_prefix(prefix, complete):
            clauses.pop(i)
            num += 1
        i -= 1
    return num

def _eliminate_tautological_variables(clauses: CNF_Formula) -> int:
    """
    PRE: clauses are ordered by the variables (absolute value of literals)

    If v (or -v) is found several times in a clause c, only one appearence is left.
    """
    num = 0
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        j = len(c) - 1
        while j > 0:
            if c[j-1] == c[j]:
                c.pop(j)
                num += 1
            j -= 1
        i -= 1
    return num


def _eliminate_tautological_clauses(clauses: CNF_Formula) -> int:
    """
    PRE: clauses are ordered by the variables absolute values

    If v and -v are in the same clause c, c is removed from clauses.
    """
    num = 0
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        num_literals = len(c)
        j = 0
        while j < num_literals - 1:
            if c[j] == -c[j+1]:
                clauses.pop(i)
                num += 1
                break
            j += 1
        i -= 1
    return num

def _unit_propagation(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> None | bool:
    i = len(clauses) - 1
    while i >= 0:
        clause = clauses[i]
        is_unit_clause = len(clause) == 1
        v = clause[0]
        is_existential_var = vars2quant[abs(v)] == 'e'
        
        if is_unit_clause and is_existential_var:
            j = len(clauses) - 1
            while j >= 0:
                if v in clauses[j]:
                    clauses.pop(j)
                elif -v in clauses[j]:
                    clauses[j].remove(-v)
                    if not clauses[j]:
                        return False
                j -= 1

            i = len(clauses) # - 1 is done outside of the 'if' 

        i -= 1

def _any_all_universal_clause(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> bool:
    for clause in clauses:
        if all( vars2quant[abs(lit)] == 'a' for lit in clause ):
            return True
    return False

def _polarity(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> None | bool:
    # v -> ( [[i,j] where clauses[i,j] == v],  [[i',j'] where clauses[i',j'] == -v])
    vars = list(vars2quant.keys())
    num_vars = len(vars)
    assert vars == list(range(1, num_vars+1)), "vars no va de 1 a n. Mal renaming o se pierde el orden al pasar a diccionario?"

    """
    polarities = [None] + [([], []) for _ in range(num_vars)]
    for i in range(len(clauses)):
        for j in range(len(clauses[i])):
            lit = clauses[i][j]
            assert lit != 0, "Ningún literal debería ser 0 !!!"
            if lit > 0:
                polarities[lit][0].append([i,j])
            else:
                polarities[-lit][1].append([i,j])
    
    for v in range(1, num_vars + 1):
        if len(polarities[v][0]) == 0:
            positions = polarities[v][1]
        elif len(polarities[v][1]) == 0:
            positions = polarities[v][0]
        
        if vars2quant[v] == 'e':
            # With reversed we don't need to keep the number of removed clauses, because clause_i are ascendent (so descendent when reversed)
            for clause_i, lit_i in reversed(positions):
                clauses.pop(clause_i)

                # Here this implementation gets complicated, since the cached positions must be updated
                for next_v in range(v + 1, num_vars + 1):
                    p_index = len(polarities[next_v])
                    while p_index >= 0 and polarities[next_v]
                    for clause_j, lit_j in reversed(polarities[next_v]):
                        # simply removing is not enough, because we may detect more vars with same polarity than those that really are
                        if clause_j == clause_i: 

        else:
            assert vars2quant[v] == 'a', "Cuantificador desconocido !!!"
            for clause_i, lit_i in positions:
                clauses[clause_i].pop(lit_i)
                if not clauses[clause_i]:
                    return False
    """

    for v in range(1, num_vars):
        polarities = ([], [])
        for i in range(len(clauses)):
            for j in range(len(clauses[i])):
                lit = clauses[i][j]
                assert lit != 0, "Ningún literal debería ser 0 !!!"
                if lit == v:
                    polarities[0].append([i,j])
                elif lit == -v:
                    polarities[1].append([i,j])
        
        if len(polarities[0]) == 0:
            positions = polarities[1]
        elif len(polarities[1]) == 0:
            positions = polarities[0]
        else:
            # Either the case of a quantified variable that doesn't appear in the clauses
            # or the case of a variable with both polarities
            continue

        if vars2quant[v] == 'e':
            # With reversed we don't need to keep the number of removed clauses, because clause_i are ascendent (so descendent when reversed)
            for clause_i, lit_i in reversed(positions):
                clauses.pop(clause_i)
        else:
            assert vars2quant[v] == 'a', "Cuantificador desconocido !!!"
            for clause_i, lit_i in positions:
                clauses[clause_i].pop(lit_i)
                if not clauses[clause_i]:
                    return False


def _preprocess(clauses: CNF_Formula, quantifiers: List[QBlock]) -> None | bool:
    vars2quant = {}
    for q, vars in quantifiers:
        for v in vars:
            vars2quant[v] = q

    """
    Orden más apropiado de las simplificaciones:
    1. Polaridad: si una variable siempre aparece con la misma polaridad
        a) Es existencial, eliminamos las cláusulas donde aparece
        b) Es universal, eliminamos los literales (comprobando si queda una cláusula vacía -> False)
    2. Unit propagation con variables existenciales
        a) Eliminación de las cláusulas donde aparece el literal con la misma polaridad que en el 
           unit-clause (incluyendo el propio unit-clause)
        b) Eliminación de los literales con polaridad inversa en el resto de cláusulas (comprobando
           si queda alguna cláusula vacía -> False)
    3. Cláusulas con todo variables universales: si hay alguna cláusula compuesta únicamente por 
       variables universales -> False

    (3) no modifica las clásulas, sólo hace un chequeo. Por tanto, no simplifica la fórmula para que
    las demás transformaciones puedan simplificar todavía más la fórmula.

    (2) puede hacer que aparezcan más unit-clauses iterativamente, por lo que hay que ejecutarlo
    varias veces. También puede hacer que aparezcan cláusulas con variables universales al eliminar
    variables existenciales. Por tanto, conviene ejecutarlo antes de (3). Por otro lado, al detectar
    una variable de una unit-clause, se eliminan todas sus apariciones de la fórmula. Por tanto, si 
    dicha variable hubiera tenido la misma polaridad en toda la fórmula, la fórmula se simplifica de 
    la misma manera que con (1). No obstante, ejecutar primero (2) no ayuda a (1), ya que como elimina
    todas las apariciones de una variable y no sólo literales de una polaridad concreta de dicha variable,
    no genera variables que antes no tenían la misma polaridad y ahora sí.

    (1) puede coincider con (2) en el caso antes mencionado. Pero, en cuanto a las variables universales,
    puede hacer aparecer nuevos unit-clauses de variables existenciales, por lo que conviene ejecutarlo
    antes de (2). Por otro lado, si la variable existencial eliminada estuviera en una cláusula con otras
    variables universales (o sóla, dando como resultado False por cláusula vacía), la cláusula restante
    seguirá componiéndose únicamente por variables universales, por lo que (3) no es afectada.

    En conclusión, el orden para evitar varias llamadas iterativas a la misma simplificación sin perder
    por ello potenciales simplificaciones es 1-2-3, donde (2) sí que es iterativo sólo consigo mismo.
                                                   _
                                                  \ /
    Grafo de permitir siplificaciones extra:  1 -> 2 -> 3        
    """

    # In place modification to clauses
    if _polarity(clauses, vars2quant) is False:
        return False
    # In place modification to clauses
    if _unit_propagation(clauses, vars2quant) is False:
        return False
    
    if _any_all_universal_clause(clauses, vars2quant):
        return False
    

def compactify(clauses: CNF_Formula, quantifiers: List[QBlock], 
               cached:bool, absorb_with_prefixes = False, 
               simplify_tautologies = True, preprocess = False, 
               simplify = False,
               check_absorb_with_prefixes = False) -> Tuple | bool:
    """
    The idea is to have a ternary tree with a level for each variable in the CNF.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    if simplify_tautologies:
        # set_trace()
        _eliminate_tautological_clauses(clauses)
        _eliminate_tautological_variables(clauses)
    else:
        num = _eliminate_tautological_clauses(clauses)
        assert num == 0, "Todavía hay cláusulas con v y -v !!!"
        num = _eliminate_tautological_variables(clauses)
        assert num == 0, "Todavía hay cláusulas con varios v !!!"

    if preprocess:
        # In place modification to clauses
        if _preprocess(clauses, quantifiers) is False:
            return False
        
    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(_cmp_clauses))

    # Third: we use associativity and absortion to remove clauses that have other clause(s) (the preceeding one do to the
    # previous sorting) as prefix(es)
    if absorb_with_prefixes:
        _absorb_with_prefixes(clauses)
    if check_absorb_with_prefixes:
        num = _absorb_with_prefixes(clauses)
        assert num == 0, "No se han aplicado todas las subsumpciones (absorbciones) posibles !!!"
    # Note: the previous step is not strictly necessary. We would reach a point were the empty list would
    # be found as the base case in _compactify, and we would obtain a totally equivalent answer.

    return _compactify(clauses, cached=cached, simplify=simplify)
    

def _compactify(clauses: CNF_Formula, cached: bool, simplify = False) -> int | bool:
    """
    Auxiliar recursive function for compactify.

    PRE: clauses already ordered as desired and prefixes have absorbed complete ones.
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

    absTree = _compactify(phi3, cached=cached, simplify=simplify)
    if absTree is False:
        return False
    negTree = _compactify(phi1, cached=cached, simplify=simplify)
    posTree = _compactify(phi2, cached=cached, simplify=simplify)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o int-ID
    
    #set_trace()
    phi = CCNF.create_node(vn, negTree, posTree, absTree, cached=cached)
    if simplify:
        return CCNF.simplify_ccnf(phi, cached=cached)
    else:
        return phi

#########################################################################################
### TESTS
#########################################################################################

def test_compactify():
    print("TEST COMPACTIFY...")
    clauses_true = []
    clauses_false = [[]]

    tree_true = compactify(deepcopy(clauses_true))
    assert tree_true is True, "No hemos conseguido el árbol true a partir de lista vacía!!!"
    tree_false = compactify(deepcopy(clauses_false))
    assert tree_false is False, "No hemos conseguido el árbol false a partir de cláusula vacía!!!"

    clauses1 = [[1]]
    tree = compactify(clauses1)
    CCNF.pretty_print(tree)

    clauses2 = [[-2], [2,1], [-1]]
    tree = compactify(clauses2)
    CCNF.pretty_print(tree)

    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    tree = compactify(clauses3)
    CCNF.pretty_print(tree)
    print('-' * 50)

def test_no_absortion_needed():
    print("TEST NO ABSORTION NEEDED...")
    clauses = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    clauses_copy = deepcopy(clauses)

    tree = compactify(clauses)
    tree_no_absortion = compactify(clauses_copy, absorb_with_prefixes=False)
    
    assert tree == tree_no_absortion, "No hemos conseguido el mismo árbol sin absorción!!!"
    print('-' * 50)

def test_deepcopyable():
    print("TEST DEEPCOPYABLE...")
    clauses = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    tree = compactify(clauses)
    tree_copy = deepcopy(tree)

    assert tree == tree_copy, "No hemos conseguido el mismo árbol con deepcopy!!!"
    set_trace()
    
    tree_modified = (1, *tree_copy[1:])
    assert tree != tree_modified, "También se ha modificado el árbol original!!!"
    
    assert tree is not tree_copy, "Son la misma instancia!!!"
    # FALSE: WITH TUPLES (IMMUTABLE), THE SAME INSTANCE IS RETURNED, NO COPY IS CREATED!
    print('-' * 50)

def test_ccnf_conjunction():
    print("TEST C-CNF CONJUNCTION...")
    clauses_true = []
    clauses_false = [[]]
    clauses1 = [[1]]
    clauses2 = [[-2], [2,1], [-1]]
    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]

    tree1 = compactify(deepcopy(clauses_true))
    tree2 = compactify(deepcopy(clauses3))
    conj = CCNF.conjunction(tree1, tree2)
    assert conj == tree2, "No hemos conseguido conjunción con True"

    tree1 = compactify(deepcopy(clauses_false))
    #tree2 = compactify(deepcopy(clauses3))
    conj = CCNF.conjunction(tree1, tree2)
    assert conj == False, "No hemos conseguido conjunción con False"
    
    tree1 = compactify(deepcopy(clauses1))
    tree2 = compactify(deepcopy(clauses2))
    conj = CCNF.conjunction(tree1, tree2)
    CCNF.pretty_print(conj)

    tree1 = compactify(deepcopy(clauses2))
    tree2 = compactify(deepcopy(clauses3))
    conj = CCNF.conjunction(tree1, tree2)
    CCNF.pretty_print(conj)
    print('-' * 50)

def test_equivalent_to_false():
    print("TEST EQUIVALENT TO FALSE...")
    clauses = [[-2], [2,1], [-1]]
    tree = compactify(clauses)
    CCNF.pretty_print(tree)
    # Efectivamente, pese a que las cláusulas son equivalentes a False directamente,
    # nuestro algoritmo compactify no es capaz de simplificarlo al literal False

    clauses2 = [[-2, 1]]
    tree2 = compactify(clauses2)
    CCNF.pretty_print(tree2)

    conj = CCNF.conjunction(tree, tree2)
    CCNF.pretty_print(conj)
    assert tree == conj, "No hemos conseguido que la conjunción sea igual al completo equivalente a False!!!"
    # Efectivamente, al hacer conjunción conseguimos un árbol igual al original, pero no el literal False!
    print('-' * 50)

def test_ccnf_disjunction():
    print("TEST C-CNF DISJUNCTION...")
    clauses_true = []
    clauses_false = [[]]
    clauses1 = [[1]]
    clauses2 = [[-2], [2,1], [-1]]
    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]

    tree1 = compactify(deepcopy(clauses_true))
    tree2 = compactify(deepcopy(clauses3))
    disj = CCNF.disjunction(tree1, tree2)
    assert disj == True, "No hemos conseguido disyunción con True"

    tree1 = compactify(deepcopy(clauses_false))
    #tree2 = compactify(deepcopy(clauses3))
    disj = CCNF.disjunction(tree1, tree2)
    assert disj is tree2, "No hemos conseguido disyunción con False"
    
    tree1 = compactify(deepcopy(clauses1))
    tree2 = compactify(deepcopy(clauses2))
    disj = CCNF.disjunction(tree1, tree2)
    CCNF.pretty_print(disj)

    tree1 = compactify(deepcopy(clauses2))
    tree2 = compactify(deepcopy(clauses3))
    disj = CCNF.disjunction(tree1, tree2)
    CCNF.pretty_print(disj)
    print('-' * 50)

###################
def get_total_size(obj, seen=None):
    """
    Calcula el tamaño total de un objeto y sus elementos anidados de forma recursiva.
    Evita la doble cuenta de objetos compartidos mediante 'seen' (conjunto de IDs).
    """
    if seen is None:
        seen = set()
    obj_id = id(obj)
    if obj_id in seen:
        return 0  # Ya contamos este objeto
    seen.add(obj_id)

    size = getsizeof(obj)

    if isinstance(obj, dict):
        size += sum(get_total_size(k, seen) + get_total_size(v, seen) for k, v in obj.items())
    elif hasattr(obj, '__iter__') and not isinstance(obj, (str, bytes, bytearray)):
        # Si es iterable (no string/bytes para evitar iterar caracteres/bytes)
        size += sum(get_total_size(item, seen) for item in obj)
    elif hasattr(obj, '__dict__'): # Para instancias de clases personalizadas
        size += get_total_size(obj.__dict__, seen) # Sumar el diccionario de atributos
    # Puedes añadir más condiciones para otros tipos específicos si es necesario
    return size
###################

def test_memory_sizes():
    TEST_DIR = './Test_works/'
    directory_sat = TEST_DIR + "sat"
    instance1 = directory_sat + "/r_100_80_11.qdimacs"
    instance2 = directory_sat + "/b.q"

    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    print(f"Total size of {instance2}: {get_total_size(clauses)}")
    tree = compactify(clauses)
    print(f"Total size of the tree: {get_total_size(tree)}")
    print(f"Depth of the tree: {CCNF.depth(tree)}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {CCNF.max_nodes(tree)}")
    print(f"Actual number of nodes: {CCNF.nodes(tree)}")

    print("-" * 30)

    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    print(f"Total size of {instance2}: {get_total_size(clauses)}")
    tree = compactify(clauses)
    print(f"Total size of the tree: {get_total_size(tree)}")
    print(f"Depth of the tree: {CCNF.depth(tree)}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {CCNF.max_nodes(tree)}")
    print(f"Actual number of nodes: {CCNF.nodes(tree)}")

def test_depth_x1():
    x1 = (1, True, False, True)
    depth = CCNF.depth(x1)
    print(f"Depth of x1 = {depth}")

if __name__ == '__main__':
    #test_compactify()
    #test_no_absortion_needed()
    #test_deepcopyable()
    #test_equivalent_to_false()
    #test_ccnf_conjunction()
    #test_ccnf_disjunction()
    test_memory_sizes()
    #test_depth_x1()
    pass