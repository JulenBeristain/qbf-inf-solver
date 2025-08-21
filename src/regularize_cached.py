# regularize_cached.py

##############################################################################################
### IMPORTS ##################################################################################

from functools import cmp_to_key, lru_cache
from pdb import set_trace
from sys import getsizeof
from collections import deque
from .total_size import get_total_size
from .types_qbf import *

##############################################################################################
### BOOLEAN OPERATIONS AND FORMULA SIMPLIFICATIONS WITH RCNFs ################################

class RCNF:
    """
    Class that contains only static methods to work with nested 4-tuples (id + ternary tree)
    that represent formulas in the RCNF form. In this version, the ternary tree is not composed
    of nested tuples. Instead, each node is identified with an integer, so a node is just a 
    4-tuple of four ints (the variable, and the three IDs of the root nodes of the subtrees, or
    a boolean value, if the subtree is a leaf). Two dicts are used to map IDs to subformulas and
    viceversa.

    Note: a microoptimization would be to delete this class altogether and define all the following
        static methods as free functions. The advantage of this class is the ease of importing
        all these functions. In the final version, it is indeed removed, so the extra indirection
        of this class is avoided.
    """
    
    ##########################################################################################
    ### COUNT NODE CREATION ##################################################################

    # Note: Key detail for this implementation: bool is a subtype of int, so True and 1 are 
    # not distinguished when used as dict keys. Therefore, we start IDs from 2 (see in 
    # create_node that this initial value of 1 is not taken into account).
    _next_id = 1

    # Note: this static variable and getter/setter function are for debugging purposes only.

    def num_nodes_created():
        """
        Public function to access the number of created nodes.

        Returns:
            int: number of nodes created until the call (current value of _next_id - 1).
        """
        return RCNF._next_id - 1

    def num_current_nodes():
        """
        Public that restarts the count of created nodes.
        """
        return len(RCNF.id2tuple)
    
    def restart_node_counter():
        RCNF._next_id = 1
   
    ##########################################################################################
    ### NODE CREATION AND CLEANUP ############################################################

    tuple2id = {}
    id2tuple = {}

    def reset_nodes() -> None:
        """
        Function that clears the IDs used till the call, the caches that map IDs to 
        subformulas and viceversa, and the memoization caches of the boolean operations.
        """
        RCNF.tuple2id.clear()
        RCNF.id2tuple.clear()
        RCNF._next_id = 1
        RCNF.conjunction_cache.clear()
        RCNF.disjunction_cache.clear()

    def _collect_reachable_nodes(root_id: int) -> Set[int]:
        """
        Identify all node IDs reachable from root_id using a BFS (Breadth-First Search) traversal.
        
        Args:
            root_id (int): the ID of the root of the subformula from which the BFS will start.

        Returns:
            Set[int]: the set of the IDs that correspond to the nodes that are reachable from the node identified by root_id.
        """
        reachable_ids = set()
        queue = deque([root_id]) # Usamos una cola para BFS

        while queue:
            current_id = queue.popleft() # Saca el primer ID de la cola
            if current_id in reachable_ids:
                continue # Ya visitado, lo saltamos
            reachable_ids.add(current_id)

            _, neg_tree_id, pos_tree_id, abs_tree_id = RCNF.id2tuple[current_id]
            queue.extend(id for id in (neg_tree_id, pos_tree_id, abs_tree_id) if id > 1) # Check for bools

        return reachable_ids

    def cleanup_node_dictionaries(root_id: int) -> None:
        """
        Clear the dicts id2tuple and tuple2id, removing the nodes that are not reachable from root_id.
        
        Args:
            root_id (int): the ID of the root of the complete formula. All nodes not reachable from it are going to be removed.
        """
        reachable_ids = RCNF._collect_reachable_nodes(root_id)
        
        nodes_to_remove = RCNF.id2tuple.keys() - reachable_ids
        for node_id in nodes_to_remove: # No se puede iterar sobre id2tuple porque lo modificamos
            del RCNF.id2tuple[node_id]
        
        RCNF.tuple2id = {tuple_:id for id,tuple_ in RCNF.id2tuple.items()}

        RCNF.conjunction_cache = {k:v for k,v in RCNF.conjunction_cache.items() if v not in nodes_to_remove}
        RCNF.disjunction_cache = {k:v for k,v in RCNF.disjunction_cache.items() if v not in nodes_to_remove}


    def create_node(v: PositiveInt, negTree: Union[int, bool], posTree: Union[int, bool], absTree: Union[int, bool]) -> int:
        """
        Interface function to create nodes depending on the configuration of the algorithm

        Args:
            v (PositiveInt): the variable of the node (the one of the root node for the current subformula).
            negTree (int | bool): the ID of the node that is the root of the first subtree, which is the subformula that contains ¬v, or True/False if there is none.
            posTree (int | bool): same as negTree, but for the second subtree, the subformula that contains +v.
            absTree (int | bool): same as negTree, but for the third subtree, the subformula that doesn't contain v.
            
        Returns:
            int: the ID of the created new node (the incremented value of _next_id).
        """
        
        assert absTree is not False, \
        f"Variable [{v}]: se incumple ψ3 /= false !!!"
        assert (negTree is not False) or (posTree is not False), \
            f"Variable [{v}]: se incumple ψ1 /= false or ψ2 /= false !!!"
        assert (absTree is not True) or (posTree is not True) or (negTree is not True), \
            f"Variable [{v}]: se incumple ψ1 /= true or ψ2 /= true or ψ3 /= true !!!"
        
        assert isinstance(v, int) and v > 0, f"v={v} no es un entero positivo!!! (next_id={RCNF._next_id})"
        assert isinstance(negTree, int) or isinstance(negTree, bool), f"negTree={negTree} no es int o bool!!! (next_id={RCNF._next_id})"
        assert isinstance(posTree, int) or isinstance(posTree, bool), f"posTree={posTree} no es int o bool!!! (next_id={RCNF._next_id})"
        assert isinstance(absTree, int) or isinstance(absTree, bool), f"absTree={absTree} no es int o bool!!! (next_id={RCNF._next_id})"

        node = (v, negTree, posTree, absTree)
        node_id = RCNF.tuple2id.get(node)
        if node_id is None:
            RCNF._next_id += 1
            RCNF.tuple2id[node] = RCNF._next_id
            RCNF.id2tuple[RCNF._next_id] = node
            return RCNF._next_id
        return node_id

    ##########################################################################################
    ### RCNF COMPARISON ######################################################################

    def equals(tree1: Union[int, bool], tree2: Union[int, bool]) -> bool:
        """
        Function that compares two RCNF formulas. As the formulas are identified by a unique ID,
        an int comparison is enough.

        Args:
            tree1 (int | bool): the ID of the first formula to be compared.
            tree2 (int | bool): the ID of the second formula to be compared.
            
        Returns:
            bool: True if tree1 and tree2 represent the same RCNF formula.
    
        Note: A mirooptmization would to be delete this function altogether. It is done in the final 
            version (see that it is only used in the simplify methods).
        """
        return tree1 == tree2

    ##########################################################################################
    ### BOOLEAN OPERATIONS ###################################################################

    ##########################################################################################
    ### CONJUNCTION ##########################################################################

    # For debugging
    conjunction_calls: int = 0
    def reset_conjunction_calls() -> None:
        """
        Function that resets the number of calls to conjunction.
        """
        RCNF.conjunction_calls = 0

    def conjunction(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the conjunction between the two RCNF formulas. This function is a 
        wrapper that calls to the corresponding version depending on the configuration of the algorithm.

        Args:
            tree1 (int | bool): the ID of the first formula to perform the conjunction.
            tree2 (int | bool): the ID of the second formula to perform the conjunction.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            int | bool: the ID of the RCNF formula equivalent to the conjunction of tree1 and tree2, or the bool value if it is the case.
        """
        if config['version_cached_memo_lru']:
            return RCNF.conjunction_lru(id1, id2, config)
        return RCNF.conjunction_dicts(id1, id2, config)

    ##########################################################################################
    ### CONJUNCTION MEMOIZATION WITH LRU_CACHE ###############################################

    @lru_cache(maxsize=None)
    def conjunction_lru(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the conjunction between the two RCNF formulas. In this case, the memoization
        is done with a lru_cache. The configuration determines if the resulting formula is simplified (in practice,
        we always have simplified with this version). No removal of nodes is available, since lru_cache doesn't 
        give the possibility of selectively removing certain elements.
        """
        RCNF.conjunction_calls += 1
        
        assert isinstance(id1, int) or isinstance(id1, bool), f"id1={id1} no es un ID de un nodo o un booleano!!!"
        assert isinstance(id2, int) or isinstance(id2, bool), f"id2={id2} no es un ID de un nodo o un booleano!!!"

        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if id1 is True: return id2
        if id2 is True: return id1

        # Domination (false is the dominant element of conjunction)
        if id1 is False or id2 is False: 
            return False
        
        tree1, tree2 = RCNF.id2tuple[id1], RCNF.id2tuple[id2]

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_lru(tree1[3], tree2[3], config)
            if conj_abs is False:
                return False
            conj_neg = RCNF.conjunction_lru(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_lru(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi

        # Commutativity: make sure that tree1[0] >= tree2[0] (the root variable). That way, unnecesary entries are not stored
        # Different maximum variables where tree1[0] > tree2[0]
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1
        
        conj_abs = RCNF.conjunction_lru(tree1[3], id2, config)
        if conj_abs is False:
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs)
            if config["simplify"]:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
        else:
            conj_neg = RCNF.conjunction_lru(tree1[1], id2, config)
            conj_pos = RCNF.conjunction_lru(tree1[2], id2, config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if config["simplify"]:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi

    ##########################################################################################
    ### CONJUNCTION MEMOIZATION WITH DICT ####################################################

    # id1 x id2 -> id_result
    conjunction_cache: Dict[Tuple[int, int], Union[int, bool]] = {}

    def conjunction_dicts(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the conjunction between the two RCNF formulas. In this case, the memoization
        is done with a dict. The configuration determines if the resulting formula is simplified (in practice,
        we always have simplified with this version). The removal of nodes is available, and it can be performed
        depending on the configuration in the eliminate_ function in the inf_solver module.
        """
        RCNF.conjunction_calls += 1
        
        assert isinstance(id1, int) or isinstance(id1, bool), f"id1={id1} no es un ID de un nodo o un booleano!!!"
        assert isinstance(id2, int) or isinstance(id2, bool), f"id2={id2} no es un ID de un nodo o un booleano!!!"

        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if id1 is True: return id2
        if id2 is True: return id1

        # Domination (false is the dominant element of conjunction)
        if id1 is False or id2 is False: 
            return False
        # Previous base cases are not introduced in the cache because it's more efficient to compare with 'is' than 
        # calling to 'get' with a dict. From now on, we know that both ids are ints, so the keys of our cache are always
        # 2-tuples of ints (the values can be an int or a bool).
        
        # Commutativity: make sure that tree1[0] >= tree2[0] (the root variable). That way, unnecesary entries are not stored
        tree1, tree2 = RCNF.id2tuple[id1], RCNF.id2tuple[id2]
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1

        # Cache
        cached_res = RCNF.conjunction_cache.get((id1, id2))
        if cached_res is not None:
            return cached_res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_dicts(tree1[3], tree2[3], config)
            if conj_abs is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            conj_neg = RCNF.conjunction_dicts(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_dicts(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(id1, id2)] = conj_abs
                return conj_abs # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi

        # Different maximum variables where tree1[0] > tree2[0]
        conj_abs = RCNF.conjunction_dicts(tree1[3], id2, config)
        if conj_abs is False:
            RCNF.conjunction_cache[(id1, id2)] = False
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs)
            if config["simplify"]:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi
        else:
            conj_neg = RCNF.conjunction_dicts(tree1[1], id2, config)
            conj_pos = RCNF.conjunction_dicts(tree1[2], id2, config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(id1, id2)] = conj_abs
                return conj_abs # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs)
            if config["simplify"]:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi

    ##########################################################################################
    ### DISJUNCTION ##########################################################################

    def disjunction(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the disjunction between the two RCNF formulas. This function is a 
        wrapper that calls to the corresponding version depending on the configuration of the algorithm.

        Args:
            tree1 (int | bool): the ID of the first formula to perform the disjunction.
            tree2 (int | bool): the ID of the second formula to perform the disjunction.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            int | bool: the ID of the RCNF formula equivalent to the disjunction of tree1 and tree2, or the bool value if it is the case.
        """
        if config['version_cached_memo_lru']:
            return RCNF.disjunction_lru(id1, id2, config)
        return RCNF.disjunction_dicts(id1, id2, config)
    
    ##########################################################################################
    ### DISJUNCTION MEMOIZATION WITH LRU_CACHE ###############################################

    @lru_cache(maxsize=None)
    def disjunction_lru(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the disjunction between the two RCNF formulas. In this case, the memoization
        is done with a lru_cache. The configuration determines if the resulting formula is simplified (in practice,
        we always have simplified with this version). No removal of nodes is available, since lru_cache doesn't 
        give the possibility of selectively removing certain elements.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if id1 is False: return id2
        if id2 is False: return id1

        # Domination (true is the dominant element of disjunction)
        if id1 is True or id2 is True:
            return True

        tree1, tree2 = RCNF.id2tuple[id1], RCNF.id2tuple[id2]

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_lru(tree1[3], tree2[3], config)
            if phi_3_ is False:
                return False
            
            phi_11_ = RCNF.conjunction(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_lru(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_lru(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_lru(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_lru(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
        
        # Commutativity
        # Different variables in the root where tree1[0] > tree2[0]
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1
        
        disj_abs = RCNF.disjunction_lru(tree1[3], id2, config)
        if disj_abs is False:
            return False
        disj_neg = RCNF.disjunction_lru(tree1[1], id2, config)
        disj_pos = RCNF.disjunction_lru(tree1[2], id2, config)
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o int
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs)
        if config['simplify']:
            return RCNF.simplify_rcnf(phi, config)
        else:
            return phi
    
    ##########################################################################################
    ### DISJUNCTION MEMOIZATION WITH DICT ####################################################

    # id1 x id2 -> id_result
    disjunction_cache: Dict[Tuple[int, int], Union[int, bool]] = {}
    
    def disjunction_dicts(id1: Union[int, bool], id2: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the disjunction between the two RCNF formulas. In this case, the memoization
        is done with a dict. The configuration determines if the resulting formula is simplified (in practice,
        we always have simplified with this version). The removal of nodes is available, and it can be performed
        depending on the configuration in the eliminate_ function in the inf_solver module.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if id1 is False: return id2
        if id2 is False: return id1

        # Domination (true is the dominant element of disjunction)
        if id1 is True or id2 is True:
            return True
        # For the previous cases is innecesary and less efficient to use the cache

        tree1, tree2 = RCNF.id2tuple[id1], RCNF.id2tuple[id2]
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
            id1, id2 = id2, id1

        # Cache
        cached_res = RCNF.disjunction_cache.get((id1, id2))
        if cached_res is not None:
            return cached_res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_dicts(tree1[3], tree2[3], config)
            if phi_3_ is False:
                RCNF.disjunction_cache[(id1, id2)] = False
                return False
            
            phi_11_ = RCNF.conjunction(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_dicts(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_dicts(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_dicts(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_dicts(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                RCNF.disjunction_cache[(id1, id2)] = False
                return False
            if phi_14_ is True and phi_24_ is True:
                RCNF.disjunction_cache[(id1, id2)] = phi_3_
                return phi_3_ # Ya sea True o int
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.disjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.disjunction_cache[(id1, id2)] = phi
                return phi
            
        # Different variables in the root where tree1[0] > tree2[0]
        disj_abs = RCNF.disjunction_dicts(tree1[3], id2, config)
        if disj_abs is False:
            RCNF.disjunction_cache[(id1, id2)] = False
            return False
        disj_neg = RCNF.disjunction_dicts(tree1[1], id2, config)
        disj_pos = RCNF.disjunction_dicts(tree1[2], id2, config)
        if disj_neg is False and disj_pos is False:
            RCNF.disjunction_cache[(id1, id2)] = False
            return False
        if disj_neg is True and disj_pos is True:
            RCNF.disjunction_cache[(id1, id2)] = disj_abs
            return disj_abs # Ya sea True o int
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs)
        if config['simplify']:
            res = RCNF.simplify_rcnf(phi, config)
            RCNF.disjunction_cache[(id1, id2)] = res
            return res
        else:
            RCNF.disjunction_cache[(id1, id2)] = phi
            return phi

    ###########################################################################################
    ### RCNF SIMPLIFICATION ###################################################################

    def simplify_rcnf(tree: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Function that calculates the simplification of the RCNF formula identified by tree. This is 
        a wrapper function that calls to the recursive of iterative version depending on the configuration
        of the algorithm. The simplifications that are performed are:

        1. If the first two subformulas are equal, the formula is equivalent to the conjunction between that and the third subformula.
            Properties: (inverse) distributivity, tautology, and True is the neutral element of conjunction
        2. If the first and third subformulas are equal, the first subformula can be replaced with True.
            Properties: absorbtion, True is the dominant element of disyunction, and then True is the neutral element of conjunction.
        3. Same as the 2, but with the second and third subformulas.

        They are performed continuosly until no one of them is applicable again.

        Args:
            tree (int | bool): the ID of the formula to be simplified.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            int | bool: the ID of the simplified RCNF formula equivalent to the formula identified by tree.
        """
        if config['iterative']:
            return RCNF.simplify_rcnf_it(tree, config)
        return RCNF.simplify_rcnf_rec(tree, config)

    def simplify_rcnf_rec(id: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Recursive version of the simplification of RCNF formulas.
        """
        #set_trace()
        # Necessary check if in the next case it is true and conjunction returns a boolean
        if id is True or id is False:
            return id

        tree = RCNF.id2tuple[id]

        if RCNF.equals(tree[1], tree[2]):
            phi = RCNF.conjunction(tree[1], tree[3], config)
            return RCNF.simplify_rcnf_rec(phi, config)

        # First condition to avoid infinite reqursion when phi_1 = phi_3 = True
        if tree[1] is not True and RCNF.equals(tree[1], tree[3]):
            phi = RCNF.create_node(tree[0], True, tree[2], tree[3])
            return RCNF.simplify_rcnf_rec(phi, config)

        # First condition to avoid infinite reqursion when phi_2 = phi_3 = True
        if tree[2] is not True and RCNF.equals(tree[2], tree[3]):
            phi = RCNF.create_node(tree[0], tree[1], True, tree[3])
            return RCNF.simplify_rcnf_rec(phi, config)
        
        return id

    def simplify_rcnf_it(id: Union[int, bool], config: Dict[str, bool]) -> Union[int, bool]:
        """
        Iterative version of the simplification of RCNF formulas.
        """
        while True:
            # Necessary check if in the next case it is true and conjunction returns a boolean
            if id is True or id is False:
                return id

            tree = RCNF.id2tuple[id]

            if RCNF.equals(tree[1], tree[2]):
                id = RCNF.conjunction(tree[1], tree[3], config)
                continue

            # First condition to avoid infinite iteration when phi_1 = phi_3 = True
            if tree[1] is not True and RCNF.equals(tree[1], tree[3]):
                id = RCNF.create_node(tree[0], True, tree[2], tree[3])
                continue

            # First condition to avoid infinite iteration when phi_2 = phi_3 = True
            if tree[2] is not True and RCNF.equals(tree[2], tree[3]):
                id = RCNF.create_node(tree[0], tree[1], True, tree[3])
                continue
            
            return id

    ##########################################################################################
    ### MEMORY TROUBLE-SHOOTING ##############################################################

    def size(tree: Union[int, bool], seen = None) -> int:
        if seen is None:
            seen = set()
        tree_id = id(tree)
        if tree_id in seen:
            return 0  # Ya contamos este objeto
        seen.add(tree_id)

        if tree is True or tree is False:
            return getsizeof(tree)
        tree_tuple = RCNF.id2tuple[tree]
        v, neg, pos, abs = tree
        return 2*(getsizeof(tree)+get_total_size(tree_tuple)) + RCNF.size(neg, seen) + RCNF.size(pos, seen) + RCNF.size(abs, seen)


#########################################################################################
### TRANSFORMATION FROM CNF -> RCNF #####################################################

from .cnf_preprocessor import (
    eliminate_tautological_clauses_ordered,
    eliminate_tautological_variables_ordered,
    preprocess_ordered, 
    cmp_clauses, 
    absorb_with_prefixes
)    

def regularize(clauses: CNF_Formula, quantifiers: List[QBlock], config: Dict[str, bool]) -> Union[int, bool]:
    """
    Function that transforms the CNF matrix of a quantified formula to RCNF, as a ternary tree with a level for
    each variable in the CNF. Although, as we store the variables in the nodes, we might have several variables
    in a level if some subformulas don't contain the variable corresponding to a given level. That way, we can 
    avoid having a complete ternary tree, which would need an exponential number of nodes. On the other hand, in
    this version we don't have nested tuples to represent the trees, but nodes uniquely identified by IDs (ints)
    and two mappings: IDs to 4-tuples of the form (v, ID_neg, ID_pos, ID_abs) and viceversa.

    Args:
        clauses (CNF_Formula): the list of lists of ints that represents the matrix of the prenex quantified formula to be transformed to RCNF.
        quantifiers (List[QBlock]): the quantifiers of the complete formula. Used in the preprocessing of prenex quantified formulas' matrices.
        config (Dict[str, bool]): the configuration of the algorithm (in this case, used to decide if we simplify the formulas that we obtain).
        
    Returns:
        int | bool: the ID of the root of the ternary tree that represents the RCNF which is equivalent to the CNF formula in clauses.
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

    return _regularize(clauses, config)
    

def _regularize(clauses: CNF_Formula, config: Dict[str, bool]) -> Union[int, bool]:
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

    absTree = _regularize(phi3, config)
    if absTree is False:
        return False
    negTree = _regularize(phi1, config)
    posTree = _regularize(phi2, config)
    if negTree is False and posTree is False:
        return False
    if negTree is True and posTree is True:
        return absTree # Ya sea True o int-ID
    
    #set_trace()
    phi = RCNF.create_node(vn, negTree, posTree, absTree)
    if config['simplify']:
        return RCNF.simplify_rcnf(phi, config)
    else:
        return phi
