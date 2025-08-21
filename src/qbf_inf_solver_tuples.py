# qbf_inf_solver_tuples.py

##############################################################################################
### IMPORTS ##################################################################################

from pdb import set_trace
import gc
from pysat.solvers import Solver
import sys
from multiprocessing import Pool

from .cnf_preprocessor import rename_variables
from .types_qbf import *
from .qbf_parser import read_qdimacs_from_file_unchecked
from .regularize_tuples import RCNF, regularize

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

def _eliminate_variables(quantifiers: List[QBlock], rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    """
    Function that eliminates quantified blocks, one variable at a time, until the formula is simplified to
    True or False. It uses conjunction and disjunction operations with subtrees in RCNF of the formula,
    depending on the quantifier of the variable that is eliminated in each step. The version of the operations
    is determined by the configuration of the algorithm.

    This is a wrapper function that calls to the recursive or iterative version depending on the 
    configuration of the algorithm.

    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        rcnf (Union[Tuple, bool]): the matrix in RCNF of the QBF formula.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns:
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    if config['iterative']:
        return _eliminate_variables_it(quantifiers, rcnf, config)
    return _eliminate_variables_rec(quantifiers, rcnf, config)

def _eliminate_variables_rec(quantifiers: List[QBlock], rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    """
    Recursive variant of the function to eliminate variables from the QBF formula in prenex normal form
    with matrix in RCNF.
    """
    if rcnf is True or rcnf is False:
        return rcnf
    
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
        psi = config['f_elim_e'](rcnf, config)
    if debugging: print("Eliminated!")
    
    # Eliminate recursively the rest of the variables
    return _eliminate_variables_rec(quantifiers, psi)

def _eliminate_variables_it(quantifiers: List[QBlock], rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    """
    Iterative variant of the function to eliminate variables from the QBF formula in prenex normal form
    with matrix in RCNF.
    """
    while True:
        #set_trace()
        if rcnf is True or rcnf is False:
            return rcnf
        
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
            rcnf = config['f_elim_e'](rcnf, config)
        if debugging: print("Eliminated!")

def elim_e_disj_conj(rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Auxiliar function to remove the innermost variable of rcnf in case that it was existentially 
    quantified. This version performs the least amount of operations: first a disjunction, and 
    second a conjunction.

    Args:
        rcnf (Union[Tuple, bool]): the matrix in RCNF of the QBF formula.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns:
        Union[Tuple, bool]: simplified matrix of rcnf after the innermost variable has been eliminated. 
    """
    debugging = config['debugging']
    if debugging: print("Disyunción...")
    psi = RCNF.disjunction(rcnf[2], rcnf[1], config)
    if debugging: print("Conjunción...")
    #set_trace()
    return RCNF.conjunction(psi, rcnf[3], config)

def elim_e_conj2_disj(rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Auxiliar function to remove the innermost variable of rcnf in case that it was existentially 
    quantified. This version performs three operations: two conjunctions followed by a disjunction.

    Args:
        rcnf (Union[Tuple, bool]): the matrix in RCNF of the QBF formula.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns:
        Union[Tuple, bool]: simplified matrix of rcnf after the innermost variable has been eliminated. 
    """
    debugging = config['debugging']
    if debugging: print("Primera conjunción...")
    psi1 = RCNF.conjunction(rcnf[2], rcnf[3], config)
    if debugging: print("Segunda conjunción...")
    psi2 = RCNF.conjunction(rcnf[1], rcnf[3], config)
    if debugging: print("Disyunción...")
    return RCNF.disjunction(psi1, psi2, config)

def parallel_elim_e_conj2_disj(rcnf: Union[Tuple, bool], config: Dict[str, bool]) -> Union[Tuple, bool]:
    """
    Auxiliar function to remove the innermost variable of rcnf in case that it was existentially 
    quantified. This version performs three operations with a nuance: two conjunctions IN PARALLEL and
    a disjunction. 

    Args:
        rcnf (Union[Tuple, bool]): the matrix in RCNF of the QBF formula.
        config (Dict[str, bool]): configuration of the algorithm.

    Returns:
        Union[Tuple, bool]: simplified matrix of rcnf after the innermost variable has been eliminated. 
    """
    debugging = config['debugging']
    if debugging: print("Conjunciones (2) en paralelo")
    with Pool(processes=2) as pool:
        async_psi1 = pool.apply_async(RCNF.conjunction_serial_wrapper, (rcnf[2], rcnf[3], config))
        async_psi2 = pool.apply_async(RCNF.conjunction_serial_wrapper, (rcnf[1], rcnf[3], config))
        psi1, psi2 = async_psi1.get(), async_psi2.get()
    if debugging: print("Disyunción...")
    return RCNF.disjunction(psi1, psi2, config)

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
    rcnf = regularize(clauses, quantifiers, config)
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
        
        # elim_e_conj2_disj | elim_e_disj_conj | parallel_elim_e_conj2_disj
        'f_elim_e'                          : elim_e_disj_conj,
        
        'simplify'                          : True,    # Afecta a regularize, conjunction y disjunction
        
        'preprocessor'                      : True,
        
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
        'f_conjunction_serial'              : RCNF.conjunction_serial_manual_ids,
        # disjunction_serial_basic | disjunction_serial (lru) | disjunction_serial_manual | disjunction_serial_manual_ids
        'f_disjunction_serial'              : RCNF.disjunction_serial_manual_ids,

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

    possible_f_elim_e = [elim_e_conj2_disj, elim_e_disj_conj, parallel_elim_e_conj2_disj]
    assert config['f_elim_e'] in possible_f_elim_e, "Incorrect configuration! [10]"
    possible_f_conj_serial = [RCNF.conjunction_serial_basic, RCNF.conjunction_serial, 
                              RCNF.conjunction_serial_manual, RCNF.conjunction_serial_manual_ids]
    assert config['f_conjunction_serial'] in possible_f_conj_serial, "Incorrect configuration! [11]"
    possible_f_disj_serial = [RCNF.disjunction_serial_basic, RCNF.disjunction_serial, 
                              RCNF.disjunction_serial_manual, RCNF.disjunction_serial_manual_ids]
    assert config['f_disjunction_serial'] in possible_f_disj_serial, "Incorrect configuration! [12]"
    
    assert config['cached_nodes'] or (config['f_conjunction_serial'] != RCNF.conjunction_serial_manual_ids), "Incorrect configuration! [13]"
    assert config['cached_nodes'] or (config['f_disjunction_serial'] != RCNF.disjunction_serial_manual_ids), "Incorrect configuration! [14]"


    sys.setrecursionlimit(5000)
    print('SAT' if inf_solver(quantifiers, clauses, config) else 'UNSAT')
    