# compactify.py

from functools import cmp_to_key
from pdb import set_trace
from types_qbf import *
from functools import lru_cache

##############################################################################################
### COMPACTIFY ###############################################################################

@lru_cache(maxsize=None)
def create_node(v: PositiveInt, negTree: Union[Tuple, bool], posTree: Union[Tuple, bool], absTree: Union[Tuple, bool]) -> Tuple:
    return (v, negTree, posTree, absTree)

def clean_caches() -> None:
    create_node.cache_clear()
    conjunction_cache.clear()
    disjunction_cache.clear()

#######################
# BOOLEAN OPERATIONS
#######################

conjunction_cache = {}

def conjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool]) -> Union[Tuple, bool]:
    """
    Returns the conjunction between two C-CNF formulas.
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
        res = simplify_ccnf(phi)
        conjunction_cache[(tree1, tree2)] = res
        return res
        
    # Different maximum variables, where tree1[0] > tree2[0]
    conj_abs = conjunction(tree1[3], tree2)
    if conj_abs is False:
        conjunction_cache[(tree1, tree2)] = False
        return False

    phi = create_node(tree1[0], tree1[1], tree1[2], conj_abs)
    res = simplify_ccnf(phi)
    conjunction_cache[(tree1, tree2)] = res
    return res
    

disjunction_cache = {}

def disjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool]) -> Union[Tuple, bool]:
    """
    Returns the disjunction between two C-CNF formulas.
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
        res = simplify_ccnf(phi)
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
    res = simplify_ccnf(phi)
    disjunction_cache[(tree1, tree2)] = res
    return res


def simplify_ccnf(tree: Union[Tuple, bool]) -> Union[Tuple, bool]:
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

def _unit_propagation(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> Optional[bool]:
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

def _polarity(clauses: CNF_Formula, vars2quant: Dict[int, Quantifier]) -> Optional[bool]:
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
                # Break Precondition: tautological variables and clauses removed, so v is not several times in a clause, nor v and -v at the same time
                if lit == v:
                    polarities[0].append([i,j])
                    break
                elif lit == -v:
                    polarities[1].append([i,j])
                    break
        
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


def _preprocess(clauses: CNF_Formula, quantifiers: List[QBlock]) -> Optional[bool]:
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
    

def compactify(clauses: CNF_Formula, quantifiers: List[QBlock]) -> Union[Tuple, bool]:
    """
    The idea is to have a ternary tree with a level for each variable in the CNF.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    _eliminate_tautological_clauses(clauses)
    _eliminate_tautological_variables(clauses)

    # In place modification to clauses
    if _preprocess(clauses, quantifiers) is False:
        return False
        
    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(_cmp_clauses))

    return _compactify(clauses)
    

def _compactify(clauses: CNF_Formula) -> Union[Tuple, bool]:
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

    absTree = _compactify(phi3)
    if absTree is False:
        return False
    negTree = _compactify(phi1)
    posTree = _compactify(phi2)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o Tuple
    
    phi = create_node(vn, negTree, posTree, absTree)
    return simplify_ccnf(phi)

if __name__ == '__main__':
    print('NO MAIN in the "compactify" module. It is just a library with operations for the INF-solver for QBF.')
    pass