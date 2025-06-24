# compactify.py

#from __future__ import annotations # To use type hints of a class within the same class (alternative: string annotation)
from functools import cmp_to_key
from pdb import set_trace
from copy import deepcopy
from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
#from memory import get_total_size
from sys import getsizeof

##############################################################################################
### COMPACTIFY ###############################################################################

class C_CNF_Tree:
    """
    Note: this structure is identical to the one we need to implement for C-DNFs. The only things that will
        change are the interpretation of the structure (when do conjunctions and disjunctions happen), and
        possibly the management of the True and False literals in the boolean operations.
    """
    
    ###################################
    ### COUNT NODE CREATION
    _created = 0

    def num_nodes_created():
        return C_CNF_Tree._created
    
    def restart_node_counter():
        C_CNF_Tree._created = 0
    ###################################

    def __init__(self, v: PositiveInt | bool, negTree: Optional['C_CNF_Tree'], 
                 posTree: Optional['C_CNF_Tree'], absTree: Optional['C_CNF_Tree']):
        """
        PRE: the three trees have to be of the same type, C_CNF_Tree or None, no mixtures.
        """
        #if isinstance(v, bool): #sabemos que los tres subárboles serán None (o directamente los ignoramos)
        #    self.v = v
        #    self.negative = self.positive = self.absent = None
        #else:   # sabemos que ninguno de los tres subárboles será None (precondición)
        #    if absTree.is_false():
        #        self.v = False
        #        self.negative = self.positive = self.absent = None
        #    elif negTree.is_false() and posTree.is_false():
        #        self.v = False
        #        self.negative = self.positive = self.absent = None
        #    elif negTree.is_true() and posTree.is_true() and absTree.is_true():
        #        self.v = True
        #        self.negative = self.positive = self.absent = None
        #    else:
        #        self.v = v
        #        self.negative = negTree
        #        self.positive = posTree
        #        self.absent = absTree
        C_CNF_Tree._created += 1

        self.v = v
        self.negative = negTree
        self.positive = posTree
        self.absent = absTree
        # Si en algún punto llaman al constructor con estos valores, quiere decir que la fórmula no estaba
        # totalmente simplificada. Para detectar en compactify nos podría servir, pero en las operaciones 
        # booleanas somos nosotros quienes tenemos que simplificar la fórmula. Por tanto, en vez de simplemente
        # hacer assert, vamos a comprobar estas condiciones al principio de la inicialización, y devolver 
        # el árbol correspondiente al literal True o False que toque. -->
        #   --> Realmente, es mejor hacer estas comprobaciones donde se necesitan, porque podemos ahorrarnos
        #       chequeos redundantes y llamadas a operaciones innecesarias
        if isinstance(v, bool):
            assert (absTree is None) and (negTree is None) and (posTree is None)
        else:
            assert not absTree.is_false(), \
            f"Variable [{v}]: se incumple ψ3 /= false !!!"
            assert (not negTree.is_false()) or (not posTree.is_false()), \
                f"Variable [{v}]: se incumple ψ1 /= false or ψ2 /= false !!!"
            assert (not absTree.is_true()) or (not posTree.is_true()) or (not negTree.is_true()), \
                f"Variable [{v}]: se incumple ψ1 /= true or ψ2 /= true or ψ3 /= true !!!"


    def is_true(self):
        return self is C_CNF_Tree.TRUE
    
    def is_false(self):
        return self is C_CNF_Tree.FALSE

    def pretty_print(self, prefix="", child_label="Root"):
        print(f"{prefix}[{child_label}] - {self.v}") 
        if any([self.negative, self.positive, self.absent]):
            child_prefix = prefix + "   "
            self.negative.pretty_print(child_prefix, "¬")
            self.positive.pretty_print(child_prefix, "+")
            self.absent.pretty_print(child_prefix, "0")

    def __eq__(self, other):
        if not isinstance(other, C_CNF_Tree): return False
        if self.v != other.v: return False
        if self.negative != other.negative: return False
        if self.positive != other.positive: return False
        return self.absent == other.absent

    #######################
    # BOOLEAN OPERATIONS
    #######################
    def conjunction(self, other: 'C_CNF_Tree', use_direct_association: bool = False) -> 'C_CNF_Tree':
        """
        Returns the conjunction between two C-CNF formulas.
        """
        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if self.is_true(): return other
        if other.is_true(): return self

        # Domination (false is the dominant element of conjunction)
        if self.is_false(): return self
        if other.is_false(): return other

        ## Recursive cases
        # Same maximum variable in the root
        if self.v == other.v:
            conj_abs = self.absent.conjunction(other.absent)
            if conj_abs.is_false():
                return C_CNF_Tree.FALSE
            conj_neg = self.negative.conjunction(other.negative)
            conj_pos = self.positive.conjunction(other.positive)
            if conj_neg.is_false() and conj_pos.is_false():
                return C_CNF_Tree.FALSE
            if conj_abs.is_true() and conj_neg.is_true() and conj_pos.is_true():
                return C_CNF_Tree.TRUE
            return C_CNF_Tree(self.v, conj_neg, conj_pos, conj_abs)
        
        # Different maximum variables
        # Commutativity
        if self.v > other.v:
            big, little = self, other
        else:
            big, little = other, self
        # Note: no need to make a copy of little nor big because neither of them (or self and other previously) are modified.

        conj_abs = big.absent.conjunction(little)
        if conj_abs.is_false():
            return C_CNF_Tree.FALSE

        if use_direct_association:
            return C_CNF_Tree(big.v, big.negative, big.positive, conj_abs)
        else:
            conj_neg = big.negative.conjunction(little)
            conj_pos = big.positive.conjunction(little)
            if conj_neg.is_false() and conj_pos.is_false():
                return C_CNF_Tree.FALSE
            if conj_abs.is_true() and conj_neg.is_true() and conj_pos.is_true():
                return C_CNF_Tree.TRUE
            return C_CNF_Tree(big.v, conj_neg, conj_pos, conj_abs)
    
    def disjunction(self, other: 'C_CNF_Tree') -> 'C_CNF_Tree':
        """
        Returns the disjunction between two C-CNF formulas.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if self.is_false(): return other
        if other.is_false(): return self

        # Domination (true is the dominant element of disjunction)
        if self.is_true(): return self
        if other.is_true(): return other

        ## Recursive cases
        # Same maximum variable in the root
        if self.v == other.v:
            phi_11_ = other.negative.conjunction(other.absent)
            phi_21_ = other.positive.conjunction(other.absent)
            
            phi_3_ = self.absent.disjunction(other.absent)
            if phi_3_.is_false():
                return C_CNF_Tree.FALSE
            phi_12_ = self.negative.disjunction(phi_11_)
            phi_13_ = self.absent.disjunction(other.negative)
            phi_22_ = self.positive.disjunction(phi_21_)
            phi_23_ = self.absent.disjunction(other.positive)

            phi_14_ = phi_12_.conjunction(phi_13_)
            phi_24_ = phi_22_.conjunction(phi_23_)
            if phi_14_.is_false() and phi_24_.is_false():
                return C_CNF_Tree.FALSE
            if phi_3_.is_true() and phi_14_.is_true() and phi_24_.is_true():
                return C_CNF_Tree.TRUE
            return C_CNF_Tree(self.v, phi_14_, phi_24_, phi_3_)
        
        # Commutativity
        if self.v > other.v:
            big, little = self, other
        else:
            big, little = other, self

        # Note: no need to make a copy of little nor big because neither of them (or self and other previously) are modified.
        
        disj_abs = big.absent.disjunction(little)
        if disj_abs.is_false():
            return C_CNF_Tree.FALSE
        disj_neg = big.negative.disjunction(little)
        disj_pos = big.positive.disjunction(little)
        if disj_neg.is_false() and disj_pos.is_false():
            return C_CNF_Tree.FALSE
        if disj_abs.is_true() and disj_neg.is_true() and disj_pos.is_true():
            return C_CNF_Tree.TRUE
        return C_CNF_Tree(big.v, disj_neg, disj_pos, disj_abs)

    ###
    # MEMORY TROUBLE-SHOOTING
    ###
    def depth(self):
        if self.is_false() or self.is_true():
            return 1
        return 1 + max(self.negative.depth(), self.positive.depth(), self.absent.depth())

    def max_nodes(self):
        max_v = self.v
        nodes = 0
        for i in range(max_v):
            """
            max_v - 0-> nodes += 1 = 3 ** 0
            max_v - 1 -> nodes += 3 = 3 ** 1
            max_v - 2 -> nodes += 9 = 3 ** 2
            1 = max_v - (max_v - 1) -> 3 ** max_v-1
            0 -> 3 ** max_v (really only 2, TRUE and FALSE)
            """
            nodes += 3 ** i
        return nodes + 2

    """
    def nodes(self, set_nodes = None):
        if set_nodes is None:
            set_nodes = {id(self)}
            new_node = 1
        else:
            if id(self) in set_nodes:
                new_node = 0
            else:
                set_nodes.add(id(self))
                new_node = 1
        neg = 0 if self.negative is None else self.negative.nodes(set_nodes)
        pos = 0 if self.positive is None else self.positive.nodes(set_nodes)
        abs = 0 if self.absent is None else self.absent.nodes(set_nodes)
        return new_node + neg + pos + abs
    """
    def nodes(self):
        if self.is_true() or self.is_false():
            return 0
        return 1 + self.negative.nodes() + self.positive.nodes() + self.absent.nodes()

    def size(self):
        return get_total_size(self)
            
    def contains_true(self):
        if self.is_true():
            return True
        
        if self.is_false():
            return False
        
        if self.negative.contains_true():
            return True
        
        if self.positive.contains_true():
            return True
        
        if self.absent.contains_true():
            return True

        return False

    def contains_false(self):
        if self.is_false():
            return True
        
        if self.is_true():
            return False
        
        if self.negative.contains_false():
            return True
        
        if self.positive.contains_false():
            return True
        
        if self.absent.contains_false():
            return True

        return False

###
# STATIC INSTANCES OF C_CNF_TREE THAT REPRESENT TRUE AND FALSE
# The leaves of the trees are always formed by True or False literal trees
# Having them only once in memory saves some memory, we only need references to these to static constants
##
C_CNF_Tree.TRUE = C_CNF_Tree(True, None, None, None)
C_CNF_Tree.FALSE = C_CNF_Tree(False, None, None, None)

# TODO: una idea interesante inspirado en la no repetición de TRUE y FALSE sería tratar de evitar también la 
#   repetición de nodos idénticos desde abajo hasta arriba. En el caso de los nodos que directamente referencian
#   True y False tenemos 2^3=8 posibles configuraciones v-neg(T/F)-pos(T/F)-abs(T/F) por cada v (que en el nivel
#   más inferior será 1, cuidado con la necesidad de renombrar variables en previas y posteriores partes del 
#   algoritmo), pero en un árbol ternario tendremos 3^Profundidad-1 cantidad de nodos. En vez de construir un
#   nuevo nodo directamente, podemos mantener un diccionario (o una lista, ya que las variables van de 1 a n)
#   que mapea variables a nodos, y cada vez que queramos crear un nuevo nodo con v como valor, podemos mirar
#   antes si existe el nodo con la configuración neg-pos-abs que tenemos que usar. Así, en vez de construir un
#   nuevo nodo, podemos devolver directamente el que ya existe.
#   Esta aproximación puede ser más eficiente en cuanto a memoria, pero habría que ver su impacto en el coste
#   temporal. Además, habría que ver también si la repetición de los nodos es necesaria o no en los siguientes
#   pasos del algoritmo. Si es necesario, esta aproximación sería directamente inviable.

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

    TODO: decidir qué versión de Tree va a ser el final
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


def _absorb_with_prefixes(clauses: CNF_Formula) -> None:
    """
    PRE: prefixes come before the complete one.

    Note: idempotence is a concrete case of absortion.
    """
    i = len(clauses) - 1
    while i > 0:
        complete = clauses[i]
        prefix = clauses[i-1]
        if _is_prefix(prefix, complete):
            clauses.pop(i)
        i -= 1

def _eliminate_tautological_variables(clauses: CNF_Formula) -> CNF_Formula:
    """
    PRE: clauses are ordered by the variables (absolute value of literals)

    If v (or -v) is found several times in a clause c, only one appearence is left.
    """
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        j = len(c) - 1
        while j > 0:
            if c[j-1] == c[j]:
                c.pop(j)
            j -= 1
        i -= 1


def _eliminate_tautological_clauses(clauses: CNF_Formula) -> CNF_Formula:
    """
    PRE: clauses are ordered by the variables absolute values

    If v and -v are in the same clause c, c is removed from clauses.
    """
    i = len(clauses) - 1
    while i >= 0:
        c = clauses[i]
        num_literals = len(c)
        j = 0
        while j < num_literals - 1:
            if c[j] == -c[j+1]:
                clauses.pop(i)
                break
            j += 1
        i -= 1

def compactify(clauses: CNF_Formula, absorb_with_prefixes: bool = False, check_tautologies = True) -> C_CNF_Tree:
    """
    Note: this algorithm is almost identical to the one needed for C-DNFs. The only thing that changes 
        are the basic cases in _compactify, where we would need to return True instead of False and 
        viceversa.

    Note: the idea is to have a ternary tree with a level for each variable in the CNF. Nonetheless,
        it could happen that a particular phi_i does not have the next v_n-1, so in that corresponding
        subtree we will have a variable less than n-1 in the level that in theory belongs to v_n-1.
        We can interpret that the branch (the edge) "is longer" until the subtree is reached.

    CAREFUL HERE: another possibility is to enforce each level for each variable. In that case, if a 
        particular phi_i does not contain the vn corresponding to that level, simply the ¬ and + 
        branches end with a True.
        To make this implementation we would check for the same base cases as _compactify once, if
        we are not in any of those two cases we would take the greates vn (the first one), and finally
        we would perform a recursion from vn until 0 was reached.
        This second version spends more space in memory. So, unless it is necessary or helpfull to 
        implement the boolean operations more efficiently (or at all), I will stick to the first 
        implementation.
        I would say that this second version is the conceptually more clear one, and strictly 
        speaking, the one proposed in the algorithm. But I am not sure. From the point of view of
        recursion, the first one is perfectly valid (or even more) and, as said, more efficient spatially.
    """
    # First, we order each clause considering absolute values (we assume that v and -v are not in the same clause, because
    # then it would be a tautology)
    for c in clauses:
        c.sort(key=abs, reverse=True)

    if check_tautologies:
        # set_trace()
        _eliminate_tautological_clauses(clauses)
        _eliminate_tautological_variables(clauses)

    # Second, we order the clauses considering also that -v < v (for different variables we still use the absolute values)
    # Detail: lists of lists are ordered in lexicographical order (element by element until distinct ones are found, or by 
    #   length if one is prefix of the other)
    clauses.sort(key=cmp_to_key(_cmp_clauses))

    # Third: we use associativity and absortion to remove clauses that have other clause(s) (the preceeding one do to the
    # previous sorting) as prefix(es)
    if absorb_with_prefixes:
        _absorb_with_prefixes(clauses)
    # Note: the previous step is not strictly necessary. We would reach a point were the empty list would
    # be found as the base case in _compactify, and we would obtain a totally equivalent answer.
    #   Could be interesting to test if using it is faster or slower (TODO testing)

    return _compactify(clauses)
    

def _compactify(clauses: CNF_Formula) -> C_CNF_Tree:
    """
    Auxiliar recursive function for compactify.

    PRE: clauses already ordered as desired and prefixes have absorbed complete ones.
    """
    
    # Si cláusulas vacías, entonces tenemos el literal True (elemento neutro de la conjunción)
    num_clauses = len(clauses)
    if num_clauses == 0:
        return C_CNF_Tree.TRUE
    
    # Si contiene la cláusula vacía, entonces tenemos el literal False (elemento neutro de disyunción y dominante de conjunción)
    # Además, por la forma en la que hemos ordenado las cláusulas, la cláusula vacía vendrá al principio en todo caso. Por lo que 
    # es suficiente mirar la primera cláusula; el coste de esta comprobación es O(1). Y como último detalle, solo habrá una cláusula
    # vacía en todo caso, por haber absorbido los prefijos y las cláusulas idénticas.
    if len(clauses[0]) == 0:
        return C_CNF_Tree.FALSE

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
    if absTree.is_false():
        return C_CNF_Tree.FALSE
    negTree = _compactify(phi1)
    posTree = _compactify(phi2)
    if negTree.is_false() and posTree.is_false():
        return C_CNF_Tree.FALSE
    if absTree.is_true() and negTree.is_true() and posTree.is_true():
        return C_CNF_Tree.TRUE
    return C_CNF_Tree(vn, negTree, posTree, absTree)

#########################################################################################
### TESTS
#########################################################################################

def test_compactify():
    print("TEST COMPACTIFY...")
    clauses_true = []
    clauses_false = [[]]

    tree_true = compactify(deepcopy(clauses_true))
    assert tree_true.is_true(), "No hemos conseguido el árbol true a partir de lista vacía!!!"
    tree_false = compactify(deepcopy(clauses_false))
    assert tree_false.is_false(), "No hemos conseguido el árbol false a partir de cláusula vacía!!!"

    clauses1 = [[1]]
    tree = compactify(clauses1)
    tree.pretty_print()

    clauses2 = [[-2], [2,1], [-1]]
    tree = compactify(clauses2)
    tree.pretty_print()

    clauses3 = [[-1, 2, 3], [1, -2], [2, -3], [-3, 1]]
    tree = compactify(clauses3)
    tree.pretty_print()
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
    tree_copy.v += 1
    assert tree != tree_copy, "También se ha modificado el árbol original!!!"
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
    conj = tree1.conjunction(tree2)
    assert conj == tree2, "No hemos conseguido conjunción con True"

    tree1 = compactify(deepcopy(clauses_false))
    #tree2 = compactify(deepcopy(clauses3))
    conj = tree1.conjunction(tree2)
    assert conj.is_false(), "No hemos conseguido conjunción con False"
    
    tree1 = compactify(deepcopy(clauses1))
    tree2 = compactify(deepcopy(clauses2))
    conj = tree1.conjunction(tree2)
    conj.pretty_print()

    tree1 = compactify(deepcopy(clauses2))
    tree2 = compactify(deepcopy(clauses3))
    conj = tree1.conjunction(tree2)
    conj.pretty_print()
    print('-' * 50)

def test_equivalent_to_false():
    print("TEST EQUIVALENT TO FALSE...")
    clauses = [[-2], [2,1], [-1]]
    tree = compactify(clauses)
    tree.pretty_print()
    # Efectivamente, pese a que las cláusulas son equivalentes a False directamente,
    # nuestro algoritmo compactify no es capaz de simplificarlo al literal False

    clauses2 = [[-2, 1]]
    tree2 = compactify(clauses2)
    tree2.pretty_print()

    conj = tree.conjunction(tree2)
    conj.pretty_print()
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
    disj = tree1.disjunction(tree2)
    assert disj.is_true(), "No hemos conseguido disyunción con True"

    tree1 = compactify(deepcopy(clauses_false))
    #tree2 = compactify(deepcopy(clauses3))
    disj = tree1.disjunction(tree2)
    assert disj is tree2, "No hemos conseguido disyunción con False"
    
    tree1 = compactify(deepcopy(clauses1))
    tree2 = compactify(deepcopy(clauses2))
    disj = tree1.disjunction(tree2)
    disj.pretty_print()

    tree1 = compactify(deepcopy(clauses2))
    tree2 = compactify(deepcopy(clauses3))
    disj = tree1.disjunction(tree2)
    disj.pretty_print()
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
    """
    # INNECESARIO Y MAL IMPLEMENTADO YA QUE NO TIENE EN CUENTA EL ATRIBUTO __dict__  QUE TODA CLASE
    # DEFINIDA POR EL USUARIO IMPLEMENTA AUTOMÁTICAMENTE! ES DECIR, EN PYTHON LAS CLASES NO SON TUPLAS
    # DE DATOS COMO EN C/C++, SINO QUE ESTÁN IMPLEMENTADOS MEDIANTE DICCIONARIOS PARA SER MÁS DINÁMICOS!

    # OJO! Optimizable usando __slots__, y en ese punto este código pasaría a ser necesario!!!
    elif isinstance(obj, C_CNF_Tree):
        size += get_total_size(obj.v, seen)
        size += get_total_size(obj.negative, seen)
        size += get_total_size(obj.positive, seen)
        size += get_total_size(obj.absent, seen)
    """
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
    print(f"Depth of the tree: {tree.depth()}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {tree.max_nodes()}")
    print(f"Actual number of nodes: {tree.nodes()}")

    print("-" * 30)

    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    print(f"Total size of {instance2}: {get_total_size(clauses)}")
    tree = compactify(clauses)
    print(f"Total size of the tree: {get_total_size(tree)}")
    print(f"Depth of the tree: {tree.depth()}")
    print(f'Number of variables: {nv}')
    print(f"Max number of nodes: {tree.max_nodes()}")
    print(f"Actual number of nodes: {tree.nodes()}")

if __name__ == '__main__':
    #test_compactify()
    #test_no_absortion_needed()
    #test_deepcopyable()
    #test_equivalent_to_false()
    #test_ccnf_conjunction()
    #test_ccnf_disjunction()
    test_memory_sizes()
    pass