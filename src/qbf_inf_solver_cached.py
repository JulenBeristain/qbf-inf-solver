# qbf_inf_solver_cached.py

##############################################################################################
### IMPORTS ##################################################################################

from pdb import set_trace
import gc
from pysat.solvers import Solver
import sys

from .cnf_preprocessor import rename_variables
from .types_qbf import *
from .qbf_parser import read_qdimacs_from_file_unchecked
from .regularize_cached import RCNF, regularize

##############################################################################################
### SOLVER USING INDUCTIVE NORMAL FORM
##############################################################################################

##############################################################################################
### DEBUGGING GLOBAL VARIABLES ###############################################################

DB_Max_v = None
DB_Total_nodes = None
DB_Nodes = None
DB_Size = None

def reset_debugging():
    global DB_Max_v
    global DB_Total_nodes
    global DB_Nodes
    global DB_Size

    DB_Max_v = DB_Total_nodes = DB_Nodes = DB_Size = None

# Note: they are not used in the current version (see _eliminate_variables_rec/it)

##############################################################################################
### ELIMINATION OF VARIABLES #################################################################

def _eliminate_variables(quantifiers: List[QBlock], rcnf: Union[int, bool], config: Dict[str, bool]) -> bool:
    """
    Function that eliminates quantified blocks, one variable at a time, until the formula is simplified to
    True or False. It uses conjunction and disjunction operations with subtrees in RCNF of the formula,
    depending on the quantifier of the variable that is eliminated in each step. The version of the operations
    is determined by the configuration of the algorithm.

    This is a wrapper function that calls to the recursive or iterative version depending on the 
    configuration of the algorithm.

    This version uses the ID of the root node of the matrix of rcnf, and nodes are stored in dicts
    that map IDs to 4-tuples of the form (v, ID_neg, ID_pos, ID_abs) and viceversa.

    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        rcnf (Union[int, bool]): the ID of the matrix in RCNF of the QBF formula.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns:
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    if config['iterative']:
        return _eliminate_variables_it(quantifiers, rcnf, config)
    return _eliminate_variables_rec(quantifiers, rcnf, config)

def _eliminate_variables_rec(quantifiers: List[QBlock], rcnf: Union[int, bool], config: Dict[str, bool]) -> bool:
    """
    Recursive variant of the function to eliminate variables from the QBF formula in prenex normal form
    with matrix in RCNF.
    """
    if rcnf is True or rcnf is False:
        return rcnf

    rcnf = RCNF.id2tuple[rcnf]
    
    assert len(quantifiers) > 0, "NOS HEMOS QUEDADO SIN CUANTIFICADORES PERO LA FÓRMULA NO SE HA SIMPLIFICADO A TRUE O FALSE!!!"
    
    # We remove the variable, but we need to find it first
    # While loop needed in case that, due to optimizations, the rcnf tree has lost not only the root’s variable
    #set_trace()
    while rcnf[0] != quantifiers[-1][1].pop():
        if not quantifiers[-1][1]:
            quantifiers.pop()
    
    q = quantifiers[-1][0]
    assert q == 'a' or q == 'e', "CUANTIFICADOR DESCONOCIDO DETECTADO"
    
    if not quantifiers[-1][1]:
        quantifiers.pop()

    # Print debugging information
    debugging = config['debugging']
    #set_trace()
    """
    if debugging:
        max_v = rcnf[0]
        depth = RCNF.depth(rcnf)
        nodes = RCNF.nodes(rcnf)
        nodes_no_repetition = RCNF.nodes_no_repetition(rcnf)
        total_nodes = RCNF.num_nodes_created()
        size = RCNF.size(rcnf)

        if debugging:
            print("-" * 50)
            print(f"Max_v = {max_v}")
            print(f"Depth = {depth}")
            #print(f"Max_nodes = {RCNF.max_nodes(rcnf)}")
            print(f"Actual_nodes               = {nodes}")
            print(f"Actual_nodes_no_repetition = {nodes_no_repetition}")
            print(f"Total_created_nodes = {total_nodes}")
            print(f"Size = {size}")
            #objgraph.show_most_common_types()
            print(" " * 50, flush=True)

        global DB_Max_v
        global DB_Total_nodes
        global DB_Nodes
        global DB_Size

        assert DB_Max_v is None or max_v < DB_Max_v, "No se ha eliminado una variable!!!"
        if debugging and (DB_Max_v is not None and DB_Max_v - max_v != 1):
            print("Several variables have been removed at once!")
        DB_Max_v = max_v

        assert depth <= max_v + 1, "La profundidad supera el límite de la variable máxima!!!"
        
        assert nodes_no_repetition <= total_nodes, "Cómo tiene más nodos de los que se han creado?!"
        assert DB_Total_nodes is None or total_nodes >= DB_Total_nodes, "Cómo se han creado menos nodos que los que habían antes???"
        DB_Total_nodes = total_nodes

        # Too strong assert, little variations might happen
        cond = (DB_Nodes is None and DB_Size is None) or \
            (nodes_no_repetition >= DB_Nodes and size >= DB_Size) or \
            (nodes_no_repetition < DB_Nodes and size < DB_Size)
        #assert cond, "El cambio en la cantidad de nodos no coincide con el cambio en el tamaño del árbol RCNF"
        if debugging and (not cond):
            print(f"Ligera fluctuación en size: Nodos[{DB_Nodes} -> {nodes_no_repetition}] vs Size[{DB_Size} -> {size}]")
        DB_Nodes = nodes_no_repetition
        DB_Size = size
        if debugging:
            print(" " * 50, flush=True)
    #"""

    # Simplify formula
    if q == 'a':
        # INF formula (C-CNF + universal quantifier)
        if debugging:
            print("Eliminating universal...")
            print("Primera conjunción...")
        psi = RCNF.conjunction(rcnf[1], rcnf[2], config)
        if debugging: print("Segunda conjunción...")
        psi = RCNF.conjunction(psi, rcnf[3], config)
    else:
        # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
        if debugging: print("Eliminating existential...")
        if config['elim_e_disj_conj']:
            if debugging: print("Disyunción...")
            psi = RCNF.disjunction(rcnf[2], rcnf[1], config)
            if debugging: print("Conjunción...")
            psi = RCNF.conjunction(psi, rcnf[3], config)
        else:
            if debugging: print("Primera conjunción...")
            psi1 = RCNF.conjunction(rcnf[2], rcnf[3], config)
            if debugging: print("Segunda conjunción...")
            psi2 = RCNF.conjunction(rcnf[1], rcnf[3], config)
            if debugging: print("Disyunción...")
            psi = RCNF.disjunction(psi1, psi2, config)
    if debugging: print("Eliminated!")
    
    # Eliminate recursively the rest of the variables
    return _eliminate_variables_rec(quantifiers, psi)

def _eliminate_variables_it(quantifiers: List[QBlock], rcnf: Union[int, bool], config: Dict[str, bool]) -> bool:
    """
    Iterative variant of the function to eliminate variables from the QBF formula in prenex normal form
    with matrix in RCNF.
    """
    prev_num_nodes = 0
    while True:
        #set_trace()
        if rcnf is True or rcnf is False:
            return rcnf
        
        if config['version_cached_cleanup']:
            # Periódicamente conviene comprobar si hay nodos no alcanzables desde la raíz que ya no se utilizan
            num_nodes = RCNF.num_current_nodes()
            if num_nodes - prev_num_nodes > 1000:
                #print("Cleaning the dictionaries of nodes ...")
                #print(f"Number of nodes before = {num_nodes}")
                RCNF.cleanup_node_dictionaries(rcnf)
                prev_num_nodes = RCNF.num_current_nodes()
                #print(f"Number of nodes after = {prev_num_nodes}")

        rcnf = RCNF.id2tuple[rcnf]

        # We remove the variable, but we need to find it first
        # While loop needed in case that, due to optimizations, the rcnf tree has lost not only the root’s variable
        while rcnf[0] != quantifiers[-1][1].pop():
            if not quantifiers[-1][1]:
                quantifiers.pop()
        
        q = quantifiers[-1][0]
        assert q == 'a' or q == 'e', "CUANTIFICADOR DESCONOCIDO DETECTADO"
        
        if not quantifiers[-1][1]:
            quantifiers.pop()

        # Print debugging information
        debugging = config['debugging']
        #set_trace()
        """
        if debugging:
            max_v = rcnf[0]
            depth = RCNF.depth(rcnf)
            nodes = RCNF.nodes(rcnf)
            nodes_no_repetition = RCNF.nodes_no_repetition(rcnf)
            total_nodes = RCNF.num_nodes_created()
            size = RCNF.size(rcnf)

            if debugging:
                print("-" * 50)
                print(f"Max_v = {max_v}")
                print(f"Depth = {depth}")
                #print(f"Max_nodes = {RCNF.max_nodes(rcnf)}")
                print(f"Actual_nodes               = {nodes}")
                print(f"Actual_nodes_no_repetition = {nodes_no_repetition}")
                print(f"Total_created_nodes = {total_nodes}")
                print(f"Size = {size}")
                #objgraph.show_most_common_types()
                print(" " * 50, flush=True)

            global DB_Max_v
            global DB_Total_nodes
            global DB_Nodes
            global DB_Size

            assert DB_Max_v is None or max_v < DB_Max_v, "No se ha eliminado una variable!!!"
            if debugging and (DB_Max_v is not None and DB_Max_v - max_v != 1):
                print("Several variables have been removed at once!")
            DB_Max_v = max_v

            assert depth <= max_v + 1, "La profundidad supera el límite de la variable máxima!!!"
            
            assert nodes_no_repetition <= total_nodes, "Cómo tiene más nodos de los que se han creado?!"
            assert DB_Total_nodes is None or total_nodes >= DB_Total_nodes, "Cómo se han creado menos nodos que los que habían antes???"
            DB_Total_nodes = total_nodes

            # Too strong assert, little variations might happen
            cond = (DB_Nodes is None and DB_Size is None) or \
                (nodes_no_repetition >= DB_Nodes and size >= DB_Size) or \
                (nodes_no_repetition < DB_Nodes and size < DB_Size)
            #assert cond, "El cambio en la cantidad de nodos no coincide con el cambio en el tamaño del árbol RCNF"
            if debugging and (not cond):
                print(f"Ligera fluctuación en size: Nodos[{DB_Nodes} -> {nodes_no_repetition}] vs Size[{DB_Size} -> {size}]")
            DB_Nodes = nodes_no_repetition
            DB_Size = size
            if debugging:
                print(" " * 50, flush=True)
        #"""

        # Simplify formula
        if q == 'a':
            # INF formula (C-CNF + universal quantifier)
            if debugging:
                print("Eliminating universal...")
                print("Primera conjunción...")
            psi = RCNF.conjunction(rcnf[1], rcnf[2], config)
            if debugging: print("Segunda conjunción...")
            rcnf = RCNF.conjunction(psi, rcnf[3], config)
        else:
            # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
            if debugging: print("Eliminating existential...")
            if config['elim_e_disj_conj']:
                if debugging: print("Disyunción...")
                psi = RCNF.disjunction(rcnf[2], rcnf[1], config)
                if debugging: print("Conjunción...")
                #set_trace()
                rcnf = RCNF.conjunction(psi, rcnf[3], config)
            else:
                if debugging: print("Primera conjunción...")
                psi1 = RCNF.conjunction(rcnf[2], rcnf[3], config)
                if debugging: print("Segunda conjunción...")
                psi2 = RCNF.conjunction(rcnf[1], rcnf[3], config)
                if debugging: print("Disyunción...")
                rcnf = RCNF.disjunction(psi1, psi2, config)
        if debugging: print("Eliminated!")

##############################################################################################
### INF SOLVER ###############################################################################

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula, config: Dict[str, bool]) -> bool:
    """
    Function that solves a QBF instance with our algorithm that takes advantage of the operations
    that are possible with quantified formulas in Inductive Normal Form, or alternatively (if the
    innermost variable is existential), formulas in prenex normal form with the matrix in RCNF. The 
    two main steps are:
    
    1. Convert the matrix in CNF of the original formula to RCNF.
    2. Perform the elimination of variables using boolean operations with the subtrees of the matrix
        in RCNF until it simplifies to True or False.
   
    A previous renaming of the variables might be needed if the variables were not ordered in 
    the blocks of quantifiers. Other extra strategies are also used depending on the configuration 
    of the algorithm: turn off the generational garbage collection, check if we have a SAT instance
    and call to a SAT solver, and so on.

    Additionally, in this version we will work with trees which has nodes identified by
    unique IDs, with 4-tuples of the form (v, ID_neg, ID_pos, ID_abs) and two maps from
    IDs to nodes and viceversa. We won't work with nested tuples.

    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        clauses (CNF_Formula): CNF formula that we want to simplify.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns: 
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    # If we have a SAT instance, it is better to call to a SAT solver of PySAT
    if config['check_sat'] and len(quantifiers) == 1 and quantifiers[0][0] == 'e':
        with Solver(bootstrap_with=clauses) as s:
            return s.solve()
    
    if config['disable_gc']:
        # We know that there are no circular references, so we can turn off the generational garbage collection
        # Of course, the reference counting garbage collector keeps on working
        gc.disable()

    #print('Renaming variables...')
    rename_variables(quantifiers, clauses)
    #print("Finished renaming!")

    #print('Compactifying formula...')
    #t0 = time()
    # But it doesn't seem to improve so much to put regularize with simplify...
    #set_trace()
    rcnf = regularize(clauses, quantifiers, config)
    #set_trace()
    #t1 = time()
    #print('Compactified!')
    #print(f"Time: {t1 - t0 : .4f} s")

    #print("Eliminating variables...")
    #gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_UNCOLLECTABLE)
    #gc.set_debug(0)
    res = _eliminate_variables(quantifiers, rcnf, config)
    #print("Eliminated!")

    return res

##############################################################################################
### MAIN
##############################################################################################

if __name__ == '__main__':
    
    if len(sys.argv) != 2:
        print("ERROR: usage --> python3 qbf_inf_solver_tuples.py <name_instance in QDIMACS>", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    file_path = sys.argv[1]
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
    
    config = {
        'debugging'                         : False,    # No es una variante a experimentar. A False para no printear innecesariamente
        'pre_simplify_tautologies'          : True,     # Hacerlo siempre
        'iterative'                         : True,     # Hacerlo siempre (eliminate_variables y simplify)

        'conjunction_direct_association'    : True,
        
        # In this case, we only have two options, so f_elim_e
        'elim_e_disj_conj'                  : True,
        'parallel_elim_e_conj2_disj'        : None,     # Solo testearlo si elim_e_disj_conj es menos eficiente (no esperable)
        
        'simplify'                          : True,    # Afecta a regularize, conjunction y disjunction
        
        'preprocessor'                      : True,
        
        'cached_nodes'                      : None,     # Afecta a create_node -> regularize, simplify, conjunction, disjunction
        'equals_with_is'                    : None,     # Solo si cached is True
        
        'absorb_with_prefixes'              : False,
        'disable_gc'                        : True, 
        'check_sat'                         : True, 
    
        'conjunction_parallel'              : None,
        'conjunction_parallel_lazy'         : None,     # Solo aplicable si conjunction_parallel is True

        'disjunction_parallel'              : None, 
        'disjunction_parallel_conjs'        : None,     # Solo aplicable si disjunction_parallel is True
        'disjunction_parallel_disjs'        : None,     # Solo aplicable si disjunction_parallel is True
        'disjunction_parallel_total'        : None,

        # conjunction_serial_basic | conjunction_serial (lru) | conjunction_serial_manual | conjunction_serial_manual_ids
        'f_conjunction_serial'              : None,
        # disjunction_serial_basic | disjunction_serial (lru) | disjunction_serial_manual | disjunction_serial_manual_ids
        'f_disjunction_serial'              : None,

        'version_cached'                    : True,
        'version_cached_cleanup'            : False,
        # Nota: la versión lru_cache no es compatible con config, por ser éste un dict no hasheable
        'version_cached_memo_lru'           : True,     
        'version_cached_memo_dicts'         : None,     # Redundante con _lru
    }

    assert not config['debugging'], "Incorrect configuration! [1]"
    assert config['pre_simplify_tautologies'], "Incorrect configuration! [2]"
    assert config['iterative'], "Incorrect configuration! [3]"
    assert not config['version_cached_memo_lru'] or not config['version_cached_cleanup'], "Incorrect configuration! [4]"
    assert config['version_cached'], "Incorrect script (this is cached) for the set value non-cached version! [5]"
    

    sys.setrecursionlimit(5000)
    print('SAT' if inf_solver(quantifiers, clauses, config) else 'UNSAT')
    