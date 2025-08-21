# regularize_tuples.py

##############################################################################################
### IMPORTS ##################################################################################

from functools import cmp_to_key, lru_cache
from pdb import set_trace
from multiprocessing import Pool
from concurrent.futures import ProcessPoolExecutor, as_completed
import os
import psutil # To kill subprocesses in the lazy version of parallel conjunction

from .types_qbf import *

##############################################################################################
### BOOLEAN OPERATIONS AND FORMULA SIMPLIFICATIONS WITH RCNFs ################################

class RCNF:
    """
    Class that contains only static methods to work with nested 4-tuples (id + ternary tree)
    that represent formulas in the RCNF form.

    Note: a microoptimization would be to delete this class altogether and define all the following
        static methods as free functions. The advantage of this class is the ease of importing
        all these functions. In the final version, it is indeed removed, so the extra indirection
        of this class is avoided.
    """
    
    ##########################################################################################
    ### COUNT NODE CREATION ##################################################################

    # Note: this static variable and getter/setter function are for debugging purposes only.

    _created: int = 0

    def num_nodes_created() -> int:
        """
        Public function to access the number of created nodes.

        Returns:
            int: number of nodes created until the call (current value of _created).
        """
        return RCNF._created
    
    def restart_node_counter() -> None:
        """
        Public that restarts the count of created nodes.
        """
        RCNF._created = 0
    
    ##########################################################################################
    ### NODE CREATION ########################################################################

    def create_node(v: PositiveInt, negTree: Union[Tuple, bool], posTree: Union[Tuple, bool], absTree: Union[Tuple, bool], 
                    config: Dict[str, bool]) -> Tuple:
        """
        Interface function to create nodes depending on the configuration of the algorithm

        Args:
            v (PositiveInt): the variable of the node (the one of the root node for the current subformula).
            negTree (Tuple | bool): the node that is the root of the first subtree, which is the subformula that contains ¬v, or True/False if there is none.
            posTree (Tuple | bool): same as negTree, but for the second subtree, the subformula that contains +v.
            absTree (Tuple | bool): same as negTree, but for the third subtree, the subformula that doesn't contain v.
            config (Dict[str, bool]): the dict with the configuration of the algorithm.

        Returns:
            Tuple: the created new node, a 4-tuple with the main arguments.
        """
        if config['cached_nodes']:
            return RCNF.create_node_cached(v, negTree, posTree, absTree)
        else:
            return RCNF.create_node_uncached(v, negTree, posTree, absTree)

    def create_node_uncached(v: PositiveInt, negTree: Union[Tuple, bool], posTree: Union[Tuple, bool], absTree: Union[Tuple, bool]) -> Tuple:
        """
        Version that doesn't cache the created nodes, so we might have several instances for the same subformula.

        Note: if results that this version is more efficient, we could remove this function and call directly to the 
            tuple constructor. It is not (see final version).
        """
        RCNF._created += 1

        assert absTree is not False, \
        f"Variable [{v}]: se incumple ψ3 /= false !!!"
        assert (negTree is not False) or (posTree is not False), \
            f"Variable [{v}]: se incumple ψ1 /= false or ψ2 /= false !!!"
        assert (absTree is not True) or (posTree is not True) or (negTree is not True), \
            f"Variable [{v}]: se incumple ψ1 /= true or ψ2 /= true or ψ3 /= true !!!"

        return (v, negTree, posTree, absTree)

    """
    Note: It is absolutely infeasible to replace lru_cache with a manual dict tuple2tuple cache in order to clean it periodically.
    
    We would have to iterate over all the trees stored in the cache and check whether they are a subtree (at the beginning of 
    eliminate_variables) of the tree corresponding to the current formula. That would be much more expensive than in the cached version.

    Considering possible solutions, weak references could be interesting. However, with the weakref module we cannot weakly reference 
    tuples or lists, nor have dictionaries where both keys and values are weak references (only one or the other). I think the second 
    limitation could be overcome by using dicts with key-value pairs both pointing to the same weak reference created directly with 
    weakref.ref(obj), and then, at cleanup time, simply checking whether ref() = key() = value() is None and removing it from the dictionary. 
    But the first limitation is insurmountable.

    Therefore, the best option to keep avoiding the creation of repeated tuples/nodes is to use lru_cache. We could use a manual dict, 
    but since we cannot even perform periodic cleanup that way, it is better to simplify the implementation by using a tool that already 
    handles the dict. Furthermore, in this function we don't have extra parameters or ways of reordering them by commutativity that would 
    justify doing it manually.
    """

    @lru_cache(maxsize=None)
    def create_node_cached(v: PositiveInt, negTree: Union[Tuple, bool], posTree: Union[Tuple, bool], absTree: Union[Tuple, bool]) -> Tuple:
        """
        Version that caches the created nodes, so each subformula is stored uniquely in memory.
        """
        RCNF._created += 1

        assert absTree is not False, \
        f"Variable [{v}]: se incumple ψ3 /= false !!!"
        assert (negTree is not False) or (posTree is not False), \
            f"Variable [{v}]: se incumple ψ1 /= false or ψ2 /= false !!!"
        assert (absTree is not True) or (posTree is not True) or (negTree is not True), \
            f"Variable [{v}]: se incumple ψ1 /= true or ψ2 /= true or ψ3 /= true !!!"

        return (v, negTree, posTree, absTree)

    ##########################################################################################
    ### TREE VISUALIZATION ###################################################################

    def pretty_print(tree: Union[Tuple, bool], prefix="", child_label="Root"):
        if tree is True or tree is False:
            print(f"{prefix}[{child_label}] - {tree}")
            return
        
        v, neg, pos, abs = tree
        print(f"{prefix}[{child_label}] - {v}")

        child_prefix = prefix + "   "
        RCNF.pretty_print(neg, child_prefix, "¬")
        RCNF.pretty_print(pos, child_prefix, "+")
        RCNF.pretty_print(abs, child_prefix, "0")

    ##########################################################################################
    ### RCNF COMPARISON ######################################################################

    def equals(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
        """
        Function that compares two RCNF formulas. Depending on the configuration, it uses the Tuples'
        equals (recursive/iterative) function or it uses directly the is operator that compares both
        formulas' IDs. This configuration is only available if nodes are cached.

        Args:
            tree1 (Tuple | bool): the first formula to be compared.
            tree2 (Tuple | bool): the second formula to be compared.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            bool: True if tree1 and tree2 represent the same RCNF formula.
    

        Note: A mirooptmization would to be delete this function altogether. It is done in the final 
            version (see that it is only used in the simplify methods).
        """
        if config['equals_with_is']: 
            return tree1 is tree2
        return tree1 == tree2

    ##########################################################################################
    ### BOOLEAN OPERATIONS ###################################################################

    ##########################################################################################
    ### CONJUNCTION ##########################################################################

    def conjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Function that calculates the conjunction between the two RCNF formulas. This function is a 
        wrapper that calls to the corresponding version depending on the configuration of the algorithm.

        Args:
            tree1 (Tuple | bool): the first formula to perform the conjunction.
            tree2 (Tuple | bool): the second formula to perform the conjunction.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            Tuple | bool: the RCNF formula equivalent to the conjunction of tree1 and tree2.
        """
        if config['conjunction_parallel']:
            return RCNF.conjunction_parallel(tree1, tree2, config)
        else:
            return RCNF.conjunction_serial_wrapper(tree1, tree2, config)

    def conjunction_serial_wrapper(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The wrapper of the serial versions of conjunction. The function reference stored in the config
        dict is used directly.
        """
        return config['f_conjunction_serial'](tree1, tree2, config)

    ##########################################################################################
    ### CONJUNCTION PARALLEL #################################################################

    def conjunction_parallel(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The parallel version of conjunction. There are actually two variants. The first forgets about the
        early returns and performs the operations in parallel. The second one tries to keep the lazyness
        of the serial versions, which requieres a more complicated approach for process communication 
        (the most difficult part is already handled by the Python implementation of the used modules).
        """
        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if tree1 is True: return tree2
        if tree2 is True: return tree1

        # Domination (false is the dominant element of conjunction)
        if tree1 is False or tree2 is False: 
            return False

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            if not config['conjunction_parallel_lazy']:
                pool = Pool(processes=3)
                async_abs = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[3], tree2[3], config))
                async_neg = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[1], tree2[1], config))
                async_pos = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[2], tree2[2], config))
                pool.close()
                
                # Note: main problem with the parallel approach: we lost lazyness with the checks for False/True
                #       As it is now, the serial version is much more efficient
                
                pool.join()
                conj_abs, conj_neg, conj_pos = async_abs.get(), async_neg.get(), async_pos.get()
                if conj_abs is False:
                    return False
                if conj_neg is False and conj_pos is False:
                    return False
                if conj_neg is True and conj_pos is True:
                    return conj_abs # True o 
            else:
                # Note: this version where we try to include lazyness is as efficient as the first version; i.e., 
                #   less efficient than the serial version.
                pool = ProcessPoolExecutor(max_workers=3)
                futures = [ pool.submit(RCNF.conjunction_serial_wrapper, tree1[i], tree2[i], config) for i in range(1,4) ]
                
                results = [None] * 3
                for f in as_completed(futures):
                    if f is futures[0]: results[0] = f.result()
                    elif f is futures[1]: results[1] = f.result()
                    elif f is futures[2]: results[2] = f.result()
                    else:
                        print("UNKNOWN FUTURE!!!")
                        exit()
                    
                    if results[2] is False:
                        RCNF.cancel_and_kill(pool)
                        return False
                    if results[0] is False and results[1] is False:
                        RCNF.cancel_and_kill(pool)
                        return False
                    if results[0] is True and results[1] is True:
                        if results[2] is None:
                            pool.shutdown(wait=True, cancel_futures=False)
                            RCNF.kill_worker_processes()
                            return futures[2].result()
                        else:
                            RCNF.cancel_and_kill(pool)
                            return results[2]

                RCNF.cancel_and_kill(pool)
                conj_neg, conj_pos, conj_abs = results
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi


        # Different maximum variables
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1

        if config['conjunction_direct_association']:
            conj_abs = RCNF.conjunction_parallel(tree1[3], tree2, config)
            if conj_abs is False:
                return False
            
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
        
        else:
            if not config['conjunction_parallel_lazy']:
                pool = Pool(processes=3)
                async_abs = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[3], tree2, config))
                async_neg = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[1], tree2, config))
                async_pos = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree1[2], tree2, config))
                pool.close()

                pool.join()
                conj_abs, conj_neg, conj_pos = async_abs.get(), async_neg.get(), async_pos.get()
                if conj_abs is False:
                    return False
                if conj_neg is False and conj_pos is False:
                    return False
                if conj_neg is True and conj_pos is True:
                    return conj_abs # True o tuple
                
            else:
                pool = ProcessPoolExecutor(max_workers=3)
                futures = [ pool.submit(RCNF.conjunction_serial_wrapper, tree1[i], tree2, config) for i in range(1,4) ]
                
                results = [None] * 3
                for f in as_completed(futures):
                    if f is futures[0]: results[0] = f.result()
                    elif f is futures[1]: results[1] = f.result()
                    elif f is futures[2]: results[2] = f.result()
                    else:
                        print("UNKNOWN FUTURE!!!")
                        exit()
                    
                    if results[2] is False:
                        RCNF.cancel_and_kill(pool)
                        return False
                    if results[0] is False and results[1] is False:
                        RCNF.cancel_and_kill(pool)
                        return False
                    if results[0] is True and results[1] is True:
                        if results[2] is None:
                            pool.shutdown(wait=True, cancel_futures=False)
                            RCNF.kill_worker_processes()
                            return futures[2].result()
                        else:
                            RCNF.cancel_and_kill(pool)
                            return results[2]

                RCNF.cancel_and_kill(pool)
                conj_neg, conj_pos, conj_abs = results
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi

    def cancel_and_kill(pool: ProcessPoolExecutor) -> None:
        """
        Function that cancels and kills the remaining processes in pool.

        Args:
            pool (ProcessPoolExecutor): the pool of processes.
        """   
        pool.shutdown(wait=False, cancel_futures=True)
        RCNF.kill_worker_processes()

    def kill_worker_processes() -> None:
        """
        Auxiliar function that kills all the children processes of the main process of the FNI QBF solver
        algorithm.
        """
        parent = psutil.Process(os.getpid())
        children = parent.children(recursive=True)
        for child in children:
            child.kill()  # sends SIGKILL
    
    ##########################################################################################
    ### CONJUNCTION SERIAL ###################################################################

    def conjunction_serial_basic(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The serial version of conjunction. This is the most basic one. It doesn't do any kind of result memoization.
        """
        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if tree1 is True: return tree2
        if tree2 is True: return tree1

        # Domination (false is the dominant element of conjunction)
        if tree1 is False or tree2 is False: 
            return False

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_serial_basic(tree1[3], tree2[3], config)
            if conj_abs is False:
                return False
            conj_neg = RCNF.conjunction_serial_basic(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_serial_basic(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi

        # Different maximum variables
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1

        conj_abs = RCNF.conjunction_serial_basic(tree1[3], tree2, config)
        if conj_abs is False:
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
        else:
            conj_neg = RCNF.conjunction_serial_basic(tree1[1], tree2, config)
            conj_pos = RCNF.conjunction_serial_basic(tree1[2], tree2, config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi

    """
    Note: instead of lru_cache, we could use a manually created dictionary mapping (tuple1, tuple2) -> tuple_res. In this case, 
        since we use the entire nested formulas and we neither clean up nodes in the cache nor use IDs as in the 'cached' version, 
        it would not be necessary to perform manual cache cleanup either.

    On the other hand, using a manual dict could be justified for two reasons:
    1. Avoiding storing keys with boolean values, and in such basic cases using is with booleans instead.
    2. Taking advantage of commutativity by storing a single entry for any pair (tree1, tree2) 
    (i.e., not storing a separate entry for (tree2, tree1))
    
    Note 2: lru_caches can not cache dict values like config, so only a final test has been recorded in the iterative experimentation,
        where we see no relevant differences.
    """

    def clean_caches() -> None:
        """
        Auxiliar public function that cleans the created nodes cache and the memoization caches of the boolean operations. To be called
        between executions over different instances, to avoid cheating and using more memory than needed.
        """
        RCNF.create_node_cached.cache_clear()
        RCNF.conjunction_serial.cache_clear()
        RCNF.disjunction_serial.cache_clear()
        RCNF.conjunction_cache.clear()
        RCNF.disjunction_cache.clear()

    @lru_cache(maxsize=None)
    def conjunction_serial(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The serial version of conjunction that memoizes the results in a lru_cache. It can not be used directly with config, but 
        it is kept for documentation purposes.
        """
        ## Base cases
        # Identity (true is the neutral element of conjunction)
        if tree1 is True: return tree2
        if tree2 is True: return tree1

        # Domination (false is the dominant element of conjunction)
        if tree1 is False or tree2 is False: 
            return False

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_serial(tree1[3], tree2[3], config)
            if conj_abs is False:
                return False
            conj_neg = RCNF.conjunction_serial(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_serial(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi


        # Different maximum variables
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1

        conj_abs = RCNF.conjunction_serial(tree1[3], tree2, config)
        if conj_abs is False:
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
        else:
            conj_neg = RCNF.conjunction_serial(tree1[1], tree2, config)
            conj_pos = RCNF.conjunction_serial(tree1[2], tree2, config)
            if conj_neg is False and conj_pos is False:
                return False
            if conj_neg is True and conj_pos is True:
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
            
    
    conjunction_cache: Dict[Union[Tuple[int, int], Tuple[Tuple, Tuple]], Union[Tuple, bool]] = {}

    def conjunction_serial_manual(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Returns the conjunction between two C-CNF formulas. In this version, the memoization of the results is done manually with a dict.
        That way, the basic cases of bool operands are not stored and each pair of tree1-tree2 is stored only once, taking advantage
        of commutativity.
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

        res = RCNF.conjunction_cache.get((tree1, tree2))
        if res is not None:
            return res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_serial_manual(tree1[3], tree2[3], config)
            if conj_abs is False:
                RCNF.conjunction_cache[(tree1, tree2)] = False
                return False
            conj_neg = RCNF.conjunction_serial_manual(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_serial_manual(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(tree1, tree2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(tree1, tree2)] = conj_abs
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(tree1, tree2)] = res
                return res
            else:
                RCNF.conjunction_cache[(tree1, tree2)] = phi
                return phi

        # Different maximum variables, where tree1[0] > tree2[0]
        conj_abs = RCNF.conjunction_serial_manual(tree1[3], tree2, config)
        if conj_abs is False:
            RCNF.conjunction_cache[(tree1, tree2)] = False
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(tree1, tree2)] = res
                return res
            else:
                RCNF.conjunction_cache[(tree1, tree2)] = phi
                return phi
        else:
            conj_neg = RCNF.conjunction_serial_manual(tree1[1], tree2, config)
            conj_pos = RCNF.conjunction_serial_manual(tree1[2], tree2, config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(tree1, tree2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(tree1, tree2)] = conj_abs
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(tree1, tree2)] = res
                return res
            else:
                RCNF.conjunction_cache[(tree1, tree2)] = phi
                return phi

    """
    Note: cleanup with this variant would be possible by traversing the formula tree at the beginning of eliminate_, 
    collecting the IDs of the nodes used at that moment, and then traversing the memoization cache of the operations to 
    remove entries whose keys contain any IDs not found in the traversal. However, since all tuples are kept in memory 
    due to cached_nodes (the lru_cache of nodes), we would only be lightening the memoization caches. Therefore, it 
    remains of little interest.

    On the other hand, it is precisely the fact that tuples are kept in memory (in the same position) thanks to the 
    lru_cache that makes these variants possible—so the incompatibility with cleanup is something natural.
    """

    def conjunction_serial_manual_ids(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Returns the conjunction between two C-CNF formulas. In this version, the IDs of the trees are used instead of the trees 
        themselves. Only available if the nodes are being cached.
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

        id1, id2 = id(tree1), id(tree2)

        res = RCNF.conjunction_cache.get((id1, id2))
        if res is not None:
            return res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            conj_abs = RCNF.conjunction_serial_manual_ids(tree1[3], tree2[3], config)
            if conj_abs is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            conj_neg = RCNF.conjunction_serial_manual_ids(tree1[1], tree2[1], config)
            conj_pos = RCNF.conjunction_serial_manual_ids(tree1[2], tree2[2], config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(id1, id2)] = conj_abs
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi

        # Different maximum variables, where tree1[0] > tree2[0]
        conj_abs = RCNF.conjunction_serial_manual_ids(tree1[3], tree2, config)
        if conj_abs is False:
            RCNF.conjunction_cache[(id1, id2)] = False
            return False

        if config['conjunction_direct_association']:
            phi = RCNF.create_node(tree1[0], tree1[1], tree1[2], conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi
        else:
            conj_neg = RCNF.conjunction_serial_manual_ids(tree1[1], tree2, config)
            conj_pos = RCNF.conjunction_serial_manual_ids(tree1[2], tree2, config)
            if conj_neg is False and conj_pos is False:
                RCNF.conjunction_cache[(id1, id2)] = False
                return False
            if conj_neg is True and conj_pos is True:
                RCNF.conjunction_cache[(id1, id2)] = conj_abs
                return conj_abs # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], conj_neg, conj_pos, conj_abs, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.conjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.conjunction_cache[(id1, id2)] = phi
                return phi
            
    ##########################################################################################
    ### DISJUNCTION ##########################################################################

    def disjunction(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Function that calculates the disjunction between the two RCNF formulas. This function is a 
        wrapper that calls to the corresponding version depending on the configuration of the algorithm.

        Args:
            tree1 (Tuple | bool): the first formula to perform the disjunction.
            tree2 (Tuple | bool): the second formula to perform the disjunction.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            Tuple | bool: the RCNF formula equivalent to the disjunction of tree1 and tree2.
        """
        if config['disjunction_parallel']:
            #print("Versión paralelizada de disyunction")
            return RCNF.disjunction_parallel(tree1, tree2, config)
        elif config['disjunction_parallel_total']:
            return RCNF.disjunction_parallel_total(tree1, tree2, config)
        else:
            return RCNF.disjunction_serial_wrapper(tree1, tree2, config)
        
    def disjunction_serial_wrapper(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The wrapper of the serial versions of disjunction. The function reference stored in the config
        dict is used directly.
        """
        return config['f_disjunction_serial'](tree1, tree2, config)

    ##########################################################################################
    ### DISJUNCTION PARALLEL #################################################################

    def disjunction_parallel(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The parallel version of disjunction. There are two (not exclusive) possibilities. Performing the conjunctions
        that are needed in parallel, and performing the first level of disjunctions in parallel (with the serial
        version of disjunction). In this version, early returns with the third subformula is respected, so it is 
        kind of serial in that part of the execution, with the first recursive call. For the other early returns,
        the results of the parallel executions are needed, so there is no dilemma in those cases.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if tree1 is False: return tree2
        if tree2 is False: return tree1

        # Domination (true is the dominant element of disjunction)
        if tree1 is True or tree2 is True:
            return True

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_parallel(tree1[3], tree2[3], config)
            if phi_3_ is False:
                return False
            
            if config['disjunction_parallel_conjs']:
                # Paralelizar las conjunciones va mucho peor
                with Pool(processes=2) as pool:
                    async_phi_11_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree2[1], tree2[3], config))
                    async_phi_21_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree2[2], tree2[3], config))
                    phi_11_, phi_21_ = async_phi_11_.get(), async_phi_21_.get()
            else:
                phi_11_ = RCNF.conjunction(tree2[1], tree2[3], config)
                phi_21_ = RCNF.conjunction(tree2[2], tree2[3], config)
            
            if config['disjunction_parallel_disjs']:
                with Pool(processes=4) as pool:
                    async_phi_13_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2[1], config))
                    async_phi_23_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2[2], config))
                    async_phi_12_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[1], phi_11_, config))
                    async_phi_22_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[2], phi_21_, config))
                    phi_13_, phi_23_, phi_12_, phi_22_ = async_phi_13_.get(), async_phi_23_.get(), async_phi_12_.get(), async_phi_22_.get()
            else:
                phi_13_ = RCNF.disjunction_parallel(tree1[3], tree2[1], config)
                phi_23_ = RCNF.disjunction_parallel(tree1[3], tree2[2], config)
                phi_12_ = RCNF.disjunction_parallel(tree1[1], phi_11_, config)
                phi_22_ = RCNF.disjunction_parallel(tree1[2], phi_21_, config)

            if config['disjunction_parallel_conjs']:
                with Pool(processes=2) as pool:
                    async_phi_14_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (phi_12_, phi_13_, config))
                    async_phi_24_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (phi_22_, phi_23_, config))
                    phi_14_, phi_24_ = async_phi_14_.get(), async_phi_24_.get()
            else:
                phi_14_ = RCNF.conjunction(phi_12_, phi_13_, config)
                phi_24_ = RCNF.conjunction(phi_22_, phi_23_, config)

            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
            
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
        
        disj_abs = RCNF.disjunction_parallel(tree1[3], tree2, config)
        if disj_abs is False:
            return False
        
        if config['disjunction_parallel_disjs']:
            with Pool(processes=2) as pool:
                async_disj_neg = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[1], tree2, config))
                async_disj_pos = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[2], tree2, config))
                disj_neg, disj_pos = async_disj_neg.get(), async_disj_pos.get()
        else:
            disj_neg = RCNF.disjunction_parallel(tree1[1], tree2, config)
            disj_pos = RCNF.disjunction_parallel(tree1[2], tree2, config)
        
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            return RCNF.simplify_rcnf(phi, config)
        else:
            return phi


    def disjunction_parallel_total(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The other parallel version of disjunction. It is similar to the previous one but in this case instead of calling
        recursively in the case of the third subformula, we parallelize it along the first parallelizable conjunctions and disjunctions. 
        Nonetheless, when it is parallelized it is done with the serial version (because subprocess has the limitation that
        demon processes can not reinstantiate more subprocesses). Additionally, the early return of this third subformula
        is done after the parallelization of the other first boolean operations, so that means that more processes than needed
        might exist in a given moment (since each of the parallelized computations have to be finished).
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if tree1 is False: return tree2
        if tree2 is False: return tree1

        # Domination (true is the dominant element of disjunction)
        if tree1 is True or tree2 is True:
            return True

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            # A maximum of 5 concurrent processes apply_async-ed
            with Pool(processes=5) as pool:
                async_phi_3_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2[3], config))
                
                async_phi_11_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree2[1], tree2[3], config))
                async_phi_21_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (tree2[2], tree2[3], config))
                async_phi_13_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2[1], config))
                async_phi_23_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2[2], config))
                
                # Blocking - Moved here to start the other processes. Problematic to have return inside with block?
                phi_3_ = async_phi_3_.get()
                if phi_3_ is False:
                    return False

                # Which is going to finish sooner? phi_11_ or phi_21_?
                phi_11_ = async_phi_11_.get()
                async_phi_12_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[1], phi_11_, config))
                phi_21_ = async_phi_21_.get()
                async_phi_22_ = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[2], phi_21_, config))
                
                # Which is going to finish sooner? phi_13_+phi_12_ or phi_23_+phi_24_?
                phi_13_, phi_12_ = async_phi_13_.get(),  async_phi_12_.get()
                async_phi_14_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (phi_12_, phi_13_, config))
                phi_23_, phi_22_ = async_phi_23_.get(), async_phi_22_.get()
                async_phi_24_ = pool.apply_async(RCNF.conjunction_serial_wrapper, (phi_22_, phi_23_, config))
                
                phi_14_, phi_24_ = async_phi_14_.get(), async_phi_24_.get()
            
            # Outside of with
            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
            
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
        
        with Pool(processes=3) as pool:
            async_disj_abs = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[3], tree2, config))
            async_disj_neg = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[1], tree2, config))
            async_disj_pos = pool.apply_async(RCNF.disjunction_serial_wrapper, (tree1[2], tree2, config))
            disj_abs, disj_neg, disj_pos = async_disj_abs.get(), async_disj_neg.get(), async_disj_pos.get()
        
        if disj_abs is False:
            return False
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            return RCNF.simplify_rcnf(phi, config)
        else:
            return phi

    ##########################################################################################
    ### DISJUNCTION SERIAL ###################################################################

    def disjunction_serial_basic(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The serial version of disjunction. This is the most basic one. It doesn't do any kind of result memoization.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if tree1 is False: return tree2
        if tree2 is False: return tree1

        # Domination (true is the dominant element of disjunction)
        if tree1 is True or tree2 is True:
            return True

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_serial_basic(tree1[3], tree2[3], config)
            if phi_3_ is False:
                return False
            
            # NOTA: NO NECESARIAMENTE WRAPPER - SOLO SI DISJUNCTION PARALELIZA SUS DISJUNCTION!!!
            # DOS OPCIONES:
            #   A) Paralelizar conjunction, incluidos estos, y no disjunction-disj
            #   B) Paralelizar conjunction en elim_, y disjunction-disj (aquí) pero con conjunction seriales
            #   +) Paralelizar conjunction y disjunction-conj (en la práctica, parece similar a la opción A)
            phi_11_ = RCNF.conjunction_serial_wrapper(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction_serial_wrapper(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_serial_basic(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_serial_basic(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_serial_basic(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_serial_basic(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction_serial_wrapper(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction_serial_wrapper(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
            
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
        
        disj_abs = RCNF.disjunction_serial_basic(tree1[3], tree2, config)
        if disj_abs is False:
            return False
        disj_neg = RCNF.disjunction_serial_basic(tree1[1], tree2, config)
        disj_pos = RCNF.disjunction_serial_basic(tree1[2], tree2, config)
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            return RCNF.simplify_rcnf(phi, config)
        else:
            return phi

    @lru_cache(maxsize=None)
    def disjunction_serial(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        The serial version of disjunction that memoizes the results in a lru_cache. It can not be used directly with config, but 
        it is kept for documentation purposes.
        """
        ## Base cases
        # Identity (false is the neutral element of disjunction)
        if tree1 is False: return tree2
        if tree2 is False: return tree1

        # Domination (true is the dominant element of disjunction)
        if tree1 is True or tree2 is True:
            return True

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_serial(tree1[3], tree2[3], config)
            if phi_3_ is False:
                return False
            
            phi_11_ = RCNF.conjunction_serial_wrapper(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction_serial_wrapper(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_serial(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_serial(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_serial(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_serial(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction_serial_wrapper(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction_serial_wrapper(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                return False
            if phi_14_ is True and phi_24_ is True:
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                return RCNF.simplify_rcnf(phi, config)
            else:
                return phi
            
        # Commutativity
        if tree1[0] < tree2[0]:
            tree1, tree2 = tree2, tree1
        
        disj_abs = RCNF.disjunction_serial(tree1[3], tree2, config)
        if disj_abs is False:
            return False
        disj_neg = RCNF.disjunction_serial(tree1[1], tree2, config)
        disj_pos = RCNF.disjunction_serial(tree1[2], tree2, config)
        if disj_neg is False and disj_pos is False:
            return False
        if disj_neg is True and disj_pos is True:
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            return RCNF.simplify_rcnf(phi, config)
        else:
            return phi

    
    disjunction_cache: Dict[Union[Tuple[int, int], Tuple[Tuple, Tuple]], Union[Tuple, bool]] = {}

    def disjunction_serial_manual(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Returns the disjunction between two C-CNF formulas. In this version, the memoization of the results is done manually with a dict.
        That way, the basic cases of bool operands are not stored and each pair of tree1-tree2 is stored only once, taking advantage
        of commutativity.
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

        res = RCNF.disjunction_cache.get((tree1, tree2))
        if res is not None:
            return res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_serial_manual(tree1[3], tree2[3], config)
            if phi_3_ is False:
                RCNF.disjunction_cache[(tree1, tree2)] = False
                return False
            
            phi_11_ = RCNF.conjunction_serial_wrapper(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction_serial_wrapper(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_serial_manual(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_serial_manual(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_serial_manual(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_serial_manual(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction_serial_wrapper(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction_serial_wrapper(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                RCNF.disjunction_cache[(tree1, tree2)] = False
                return False
            if phi_14_ is True and phi_24_ is True:
                RCNF.disjunction_cache[(tree1, tree2)] = phi_3_
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.disjunction_cache[(tree1, tree2)] = res
                return res
            else:
                RCNF.disjunction_cache[(tree1, tree2)] = phi
                return phi
            
        # tree1[0] > tree2[0]
        disj_abs = RCNF.disjunction_serial_manual(tree1[3], tree2, config)
        if disj_abs is False:
            RCNF.disjunction_cache[(tree1, tree2)] = False
            return False
        disj_neg = RCNF.disjunction_serial_manual(tree1[1], tree2, config)
        disj_pos = RCNF.disjunction_serial_manual(tree1[2], tree2, config)
        if disj_neg is False and disj_pos is False:
            RCNF.disjunction_cache[(tree1, tree2)] = False
            return False
        if disj_neg is True and disj_pos is True:
            RCNF.disjunction_cache[(tree1, tree2)] = disj_abs
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            res = RCNF.simplify_rcnf(phi, config)
            RCNF.disjunction_cache[(tree1, tree2)] = res
            return res
        else:
            RCNF.disjunction_cache[(tree1, tree2)] = phi
            return phi


    def disjunction_serial_manual_ids(tree1: Union[Tuple, bool], tree2: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Returns the disjunction between two C-CNF formulas. In this version, the IDs of the trees are used instead of the trees 
        themselves. Only available if the nodes are being cached.
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

        id1, id2 = id(tree1), id(tree2)

        res = RCNF.disjunction_cache.get((id1, id2))
        if res is not None:
            return res

        ## Recursive cases
        # Same maximum variable in the root
        if tree1[0] == tree2[0]:
            phi_3_ = RCNF.disjunction_serial_manual_ids(tree1[3], tree2[3], config)
            if phi_3_ is False:
                RCNF.disjunction_cache[(id1, id2)] = False
                return False
            
            phi_11_ = RCNF.conjunction_serial_wrapper(tree2[1], tree2[3], config)
            phi_21_ = RCNF.conjunction_serial_wrapper(tree2[2], tree2[3], config)
            
            phi_12_ = RCNF.disjunction_serial_manual_ids(tree1[1], phi_11_, config)
            phi_13_ = RCNF.disjunction_serial_manual_ids(tree1[3], tree2[1], config)
            phi_22_ = RCNF.disjunction_serial_manual_ids(tree1[2], phi_21_, config)
            phi_23_ = RCNF.disjunction_serial_manual_ids(tree1[3], tree2[2], config)

            phi_14_ = RCNF.conjunction_serial_wrapper(phi_12_, phi_13_, config)
            phi_24_ = RCNF.conjunction_serial_wrapper(phi_22_, phi_23_, config)
            if phi_14_ is False and phi_24_ is False:
                RCNF.disjunction_cache[(id1, id2)] = False
                return False
            if phi_14_ is True and phi_24_ is True:
                RCNF.disjunction_cache[(id1, id2)] = phi_3_
                return phi_3_ # Ya sea True o Tuple
            
            phi = RCNF.create_node(tree1[0], phi_14_, phi_24_, phi_3_, config)
            if config['simplify']:
                res = RCNF.simplify_rcnf(phi, config)
                RCNF.disjunction_cache[(id1, id2)] = res
                return res
            else:
                RCNF.disjunction_cache[(id1, id2)] = phi
                return phi
            
        # tree1[0] > tree2[0]
        disj_abs = RCNF.disjunction_serial_manual_ids(tree1[3], tree2, config)
        if disj_abs is False:
            RCNF.disjunction_cache[(id1, id2)] = False
            return False
        disj_neg = RCNF.disjunction_serial_manual_ids(tree1[1], tree2, config)
        disj_pos = RCNF.disjunction_serial_manual_ids(tree1[2], tree2, config)
        if disj_neg is False and disj_pos is False:
            RCNF.disjunction_cache[(id1, id2)] = False
            return False
        if disj_neg is True and disj_pos is True:
            RCNF.disjunction_cache[(id1, id2)] = disj_abs
            return disj_abs # Ya sea True o Tuple
        
        phi = RCNF.create_node(tree1[0], disj_neg, disj_pos, disj_abs, config)
        if config['simplify']:
            res = RCNF.simplify_rcnf(phi, config)
            RCNF.disjunction_cache[(id1, id2)] = res
            return res
        else:
            RCNF.disjunction_cache[(id1, id2)] = phi
            return phi

    ###########################################################################################
    ### RCNF SIMPLIFICATION ###################################################################

    def simplify_rcnf(tree: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Function that calculates the simplification of the RCNF formula represented by tree. This is 
        a wrapper function that calls to the recursive of iterative version depending on the configuration
        of the algorithm. The simplifications that are performed are:

        1. If the first two subformulas are equal, the formula is equivalent to the conjunction between that and the third subformula.
            Properties: (inverse) distributivity, tautology, and True is the neutral element of conjunction
        2. If the first and third subformulas are equal, the first subformula can be replaced with True.
            Properties: absorbtion, True is the dominant element of disyunction, and then True is the neutral element of conjunction.
        3. Same as the 2, but with the second and third subformulas.

        They are performed continuosly until no one of them is applicable again.

        Note: note that we have used immutable tuples to identified nodes, and the most efficient
            configurations depend on that immutability. Nonethelles, if we had used lists with length 4
            instead of tuples, the cases 2 and 3 could be simplified to a simple assignment instead of a
            call to create_node (TODO, but it doesn't seem promising).

        Args:
            tree (Tuple | bool): the formula to be simplified.
            config (Dict[str, bool]): the configuration of the algorithm.

        Returns:
            Tuple | bool: the simplified RCNF formula equivalent to the formula represented by tree.
        """
        if config['iterative']:
            return RCNF.simplify_rcnf_it(tree, config)
        return RCNF.simplify_rcnf_rec(tree, config)

    def simplify_rcnf_rec(tree: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Recursive version of the simplification of RCNF formulas.
        """
        #set_trace()
        # Necessary check if in the next case it is true and conjunction returns a boolean
        if tree is True or tree is False:
            return tree

        if RCNF.equals(tree[1], tree[2], config):
            phi = RCNF.conjunction_serial_wrapper(tree[1], tree[3], config)
            return RCNF.simplify_rcnf_rec(phi, config)
        
        # First condition to avoid infinite reqursion when phi_1 = phi_3 = True
        if tree[1] is not True and RCNF.equals(tree[1], tree[3], config):
            phi = RCNF.create_node(tree[0], True, tree[2], tree[3], config)
            return RCNF.simplify_rcnf_rec(phi, config)

        # First condition to avoid infinite reqursion when phi_2 = phi_3 = True
        if tree[2] is not True and RCNF.equals(tree[2], tree[3], config):
            phi = RCNF.create_node(tree[0], tree[1], True, tree[3], config)
            return RCNF.simplify_rcnf_rec(phi, config)
        
        return tree

    def simplify_rcnf_it(tree: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
        """
        Iterative version of the simplification of RCNF formulas.
        """
        while True:
            # Necessary check if in the next case it is true and conjunction returns a boolean
            if tree is True or tree is False:
                return tree

            if RCNF.equals(tree[1], tree[2], config):
                tree = RCNF.conjunction_serial_wrapper(tree[1], tree[3], config)
                continue
            
            # First condition to avoid infinite iteration when phi_1 = phi_3 = True
            if tree[1] is not True and RCNF.equals(tree[1], tree[3], config):
                tree = RCNF.create_node(tree[0], True, tree[2], tree[3], config)
                continue

            # First condition to avoid infinite iteration when phi_2 = phi_3 = True
            if tree[2] is not True and RCNF.equals(tree[2], tree[3], config):
                tree = RCNF.create_node(tree[0], tree[1], True, tree[3], config)
                continue
            
            return tree

    ##########################################################################################
    ### MEMORY TROUBLE-SHOOTING ##############################################################

    def depth(tree: Union[Tuple, bool]) -> int:
        """
        Function that returns the depth of a RCNF-tree.

        Args:
            tree (Tuple | bool): the tree representing a RCNF formula.

        Returns:
            int: the depth of tree (a leaf is of depht 1).
        """
        if tree is False or tree is True:
            return 1
        return 1 + max(RCNF.depth(tree[1]), RCNF.depth(tree[2]), RCNF.depth(tree[3]))

    def max_nodes(tree: Union[Tuple, bool]) -> int:
        """
        Function that returns the maximum number of possible nodes based on the maximum variable (the one in the root node) 
        of a RCNF-tree.

        Args:
            tree (Tuple | bool): the tree representing a RCNF formula.

        Returns:
            int: the maximum possible number of nodes in tree.
        """
        if tree is False or tree is True:
            return 0
        
        max_v = tree[0]
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
        return nodes

    def nodes(tree: Union[Tuple, bool]) -> int:
        """
        Function that returns the actual number of nodes in tree.

        Args:
            tree (Tuple | bool): the tree representing a RCNF formula.

        Returns:
            int: the  number of nodes in tree (excluding the True and False leaves).
        """
        if tree is False or tree is True:
            return 0
        return 1 + RCNF.nodes(tree[1]) + RCNF.nodes(tree[2]) + RCNF.nodes(tree[3])

    def nodes_no_repetition(tree: Union[Tuple, bool], seen = None) -> int:
        """
        Same as the nodes function, but avoiding to count repeated nodes.
        """
        if tree is False or tree is True:
            return 0
        
        if seen is None:
            seen = set()
        
        if id(tree) in seen:
            node = 0
        else:
            node = 1
            seen.add(id(tree))

        return node + RCNF.nodes_no_repetition(tree[1], seen) \
                    + RCNF.nodes_no_repetition(tree[2], seen) \
                    + RCNF.nodes_no_repetition(tree[3], seen)


#########################################################################################
### TRANSFORMATION FROM CNF -> RCNF #####################################################

from .cnf_preprocessor import (
    eliminate_tautological_clauses_ordered,
    eliminate_tautological_variables_ordered,
    preprocess_ordered, 
    cmp_clauses, 
    absorb_with_prefixes
)

def regularize(clauses: CNF_Formula, quantifiers: List[QBlock], config: Dict[str, bool]) -> Union[Tuple, bool]:
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

    return _regularize(clauses, config)
    

def _regularize(clauses: CNF_Formula, config: Dict[str, bool]) -> Union[Tuple, bool]:
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
        return absTree # Ya sea True o Tuple
    
    phi = RCNF.create_node(vn, negTree, posTree, absTree, config)
    if config['simplify']:
        return RCNF.simplify_rcnf(phi, config)
    else:
        return phi

