# qbf_inf_solver.py

##############################################################################################
### IMPORTS ##################################################################################
import os
from pdb import set_trace
from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
#from compactify import C_CNF_Tree, compactify
from compactify_tuples import CCNF, compactify
from qbf_naive_solver import naive_solver_v1
from time import time
import gc
import objgraph
from pysat.solvers import Solver
from pysat.process import Processor
import numpy as np
from collections import defaultdict
import sys
from multiprocessing import Pool

import signal
from contextlib import contextmanager

# Definición de la excepción para el timeout
class TimeoutException(Exception):
    pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise TimeoutException("Timed out!")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0) # Deshabilita la alarma

##############################################################################################
### SOLVER USING INDUCTIVE NORMAL FORM
##############################################################################################
def _rename_variables(quantifiers: List[QBlock], clauses: CNF_Formula) -> None:
    """
    Función auxiliar que renombra las variables para que aparezcan en orden ascendente en
    'quantifiers'. Para que la cuantificación siga siendo la misma, renombramos también 
    las variables que aparecen en las cláusulas.

    TODO: para evitar esto, sería necesario exigir a los ficheros .qdimacs que las variables
        estén cuantificadas en orden. Podríamos añadirlo como requisito extra a nuestro parser
        completo, para modificar correspondientemente los ficheros de las fórmulas y guardarlas.
    """
    new = 1
    old2new = {}
    varset = set()
    for (i, (_, vars)) in enumerate(quantifiers):
        for j, v in enumerate(vars):
            assert v not in varset, f"La variable {v} está cuantificada más de una vez!"
            varset.add(v)
            
            if quantifiers[i][1][j] != new:
                quantifiers[i][1][j] = new
                old2new[v] = new
            new += 1
    
    if not old2new:
        return

    for i, clause in enumerate(clauses):
        for j, lit in enumerate(clause):
            new = old2new.get(abs(lit))
            if new is not None:
                if lit > 0:
                    clauses[i][j] = new
                else:
                    clauses[i][j] = -new

DB_Max_v = None
DB_Total_nodes = None
DB_Nodes = None
DB_Size = None

def _eliminate_variables(quantifiers: List[QBlock], ccnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    if config['iterative']:
        return _eliminate_variables_it(quantifiers, ccnf, config)
    return _eliminate_variables_rec(quantifiers, ccnf, config)

def _eliminate_variables_rec(quantifiers: List[QBlock], ccnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    """
    TODO: microoptimización, una vez testeados las variantes, quedarnos con la más eficiente y quitar los flags y comprobaciones
    """
    if ccnf is True or ccnf is False:
        return ccnf
    
    assert len(quantifiers) > 0, "NOS HEMOS QUEDADO SIN CUANTIFICADORES PERO LA FÓRMULA NO SE HA SIMPLIFICADO A TRUE O FALSE!!!"
    
    # Nos quitamos la variable, pero hay que encontrarlo primero
    # While necesario en caso de que con las optimizaciones el árbol de ccnf haya pérdido no solo la variable del root
    #set_trace()
    while ccnf[0] != quantifiers[-1][1].pop():
        if not quantifiers[-1][1]:
            quantifiers.pop()
    
    q = quantifiers[-1][0]
    assert q == 'a' or q == 'e', "CUANTIFICADOR DESCONOCIDO DETECTADO"
    
    if not quantifiers[-1][1]:
        quantifiers.pop()

    # Imprimimos la información antes de simplificar la fórmula
    debugging = config['debugging']
    #set_trace()
    #"""
    if debugging:
        max_v = ccnf[0]
        depth = CCNF.depth(ccnf)
        nodes = CCNF.nodes(ccnf)
        nodes_no_repetition = CCNF.nodes_no_repetition(ccnf)
        total_nodes = CCNF.num_nodes_created()
        size = CCNF.size(ccnf)

        if debugging:
            print("-" * 50)
            print(f"Max_v = {max_v}")
            print(f"Depth = {depth}")
            #print(f"Max_nodes = {CCNF.max_nodes(ccnf)}")
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
        #assert cond, "El cambio en la cantidad de nodos no coincide con el cambio en el tamaño del árbol CCNF"
        if debugging and (not cond):
            print(f"Ligera fluctuación en size: Nodos[{DB_Nodes} -> {nodes_no_repetition}] vs Size[{DB_Size} -> {size}]")
        DB_Nodes = nodes_no_repetition
        DB_Size = size
        if debugging:
            print(" " * 50, flush=True)
    #"""

    # Simplificamos la fórmula
    if q == 'a':
        # INF formula (C-CNF + universal quantifier)
        if debugging:
            print("Eliminating universal...")
            print("Primera conjunción...")
        psi = CCNF.conjunction(ccnf[1], ccnf[2], config)
        if debugging: print("Segunda conjunción...")
        psi = CCNF.conjunction(psi, ccnf[3], config)
    else:
        # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
        if debugging: print("Eliminating existential...")
        if config['elim_e_disj_conj']:
            if debugging: print("Disyunción...")
            psi = CCNF.disjunction(ccnf[2], ccnf[1], config)
            if debugging: print("Conjunción...")
            psi = CCNF.conjunction(psi, ccnf[3], config)
        else:
            if config['parallel_elim_e_conj2_disj']:
                if debugging: print("Conjunciones (2) en paralelo")
                with Pool(processes=2) as pool:
                    async_psi1 = pool.apply_async(CCNF.conjunction_serial_wrapper, (ccnf[2], ccnf[3], config))
                    async_psi2 = pool.apply_async(CCNF.conjunction_serial_wrapper, (ccnf[1], ccnf[3], config))
                    psi1, psi2 = async_psi1.get(), async_psi2.get()
            else:
                if debugging: print("Primera conjunción...")
                psi1 = CCNF.conjunction(ccnf[2], ccnf[3], config)
                if debugging: print("Segunda conjunción...")
                psi2 = CCNF.conjunction(ccnf[1], ccnf[3], config)
                if debugging: print("Disyunción...")
                ccnf = CCNF.disjunction(psi1, psi2, config)
    if debugging: print("Eliminated!")
    
    # Llamada recursiva para seguir eliminando variables
    return _eliminate_variables_rec(quantifiers, psi)

def _eliminate_variables_it(quantifiers: List[QBlock], ccnf: Union[Tuple, bool], config: Dict[str, bool]) -> bool:
    """
    TODO: microoptimización, una vez testeados las variantes, quedarnos con la más eficiente y quitar los flags y comprobaciones
    """
    while True:
        #set_trace()
        if ccnf is True or ccnf is False:
            return ccnf
        
        # Nos quitamos la variable, pero hay que encontrarlo primero
        # While necesario en caso de que con las optimizaciones el árbol de ccnf haya pérdido no solo la variable del root
        while ccnf[0] != quantifiers[-1][1].pop():
            if not quantifiers[-1][1]:
                quantifiers.pop()
        
        q = quantifiers[-1][0]
        assert q == 'a' or q == 'e', "CUANTIFICADOR DESCONOCIDO DETECTADO"
        
        if not quantifiers[-1][1]:
            quantifiers.pop()

        # Imprimimos la información antes de simplificar la fórmula
        debugging = config['debugging']
        #set_trace()
        """
        if debugging:
            max_v = ccnf[0]
            depth = CCNF.depth(ccnf)
            nodes = CCNF.nodes(ccnf)
            nodes_no_repetition = CCNF.nodes_no_repetition(ccnf)
            total_nodes = CCNF.num_nodes_created()
            size = CCNF.size(ccnf)

            if debugging:
                print("-" * 50)
                print(f"Max_v = {max_v}")
                print(f"Depth = {depth}")
                #print(f"Max_nodes = {CCNF.max_nodes(ccnf)}")
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
            #assert cond, "El cambio en la cantidad de nodos no coincide con el cambio en el tamaño del árbol CCNF"
            if debugging and (not cond):
                print(f"Ligera fluctuación en size: Nodos[{DB_Nodes} -> {nodes_no_repetition}] vs Size[{DB_Size} -> {size}]")
            DB_Nodes = nodes_no_repetition
            DB_Size = size
            if debugging:
                print(" " * 50, flush=True)
        """

        # Simplificamos la fórmula
        if q == 'a':
            # INF formula (C-CNF + universal quantifier)
            if debugging:
                print("Eliminating universal...")
                print("Primera conjunción...")
            psi = CCNF.conjunction(ccnf[1], ccnf[2], config)
            if debugging: print("Segunda conjunción...")
            ccnf = CCNF.conjunction(psi, ccnf[3], config)
        else:
            # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
            if debugging: print("Eliminating existential...")
            if config['elim_e_disj_conj']:
                if debugging: print("Disyunción...")
                psi = CCNF.disjunction(ccnf[2], ccnf[1], config)
                if debugging: print("Conjunción...")
                #set_trace()
                ccnf = CCNF.conjunction(psi, ccnf[3], config)
            else:
                if config['parallel_elim_e_conj2_disj']:
                    if debugging: print("Conjunciones (2) en paralelo")
                    with Pool(processes=2) as pool:
                        async_psi1 = pool.apply_async(CCNF.conjunction_serial_wrapper, (ccnf[2], ccnf[3], config))
                        async_psi2 = pool.apply_async(CCNF.conjunction_serial_wrapper, (ccnf[1], ccnf[3], config))
                        psi1, psi2 = async_psi1.get(), async_psi2.get()
                else:
                    if debugging: print("Primera conjunción...")
                    psi1 = CCNF.conjunction(ccnf[2], ccnf[3], config)
                    if debugging: print("Segunda conjunción...")
                    psi2 = CCNF.conjunction(ccnf[1], ccnf[3], config)
                    if debugging: print("Disyunción...")
                    ccnf = CCNF.disjunction(psi1, psi2, config)
        if debugging: print("Eliminated!")

def reset_debugging():
    global DB_Max_v
    global DB_Total_nodes
    global DB_Nodes
    global DB_Size

    DB_Max_v = DB_Total_nodes = DB_Nodes = DB_Size = None

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula, config: Dict[str, bool]) -> bool:
    """
    Function that receives the result of the parser and applies our QBF solver
    that takes advantage of the Inductive Normal Form.
    """
    # Si estamos tratando con una instancia de SAT, mejor llamar directamente a un SAT solver optimizado de PySAT
    if config['check_sat'] and len(quantifiers) == 1 and quantifiers[0][0] == 'e':
        with Solver(bootstrap_with=clauses) as s:
            return s.solve()
    
    if config['disable_gc']:
        # Sabemos que no hay referencias circulares, por lo que desactivamos el garbage collector generacional
        # Por supuesto, el garbage collector con el counter de las referencias sigue trabajando
        gc.disable()

    #print('Renaming variables...')
    _rename_variables(quantifiers, clauses)
    #print("Finished renaming!")

    #print('Compactifying formula...')
    #t0 = time()
    # But it doesn't seem to improve so much to put compactify with simplify...
    ccnf = compactify(clauses, quantifiers, config)
    #t1 = time()
    #print('Compactified!')
    #print(f"Time: {t1 - t0 : .4f} s")

    #print("Eliminating variables...")
    #gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_UNCOLLECTABLE)
    #gc.set_debug(0)
    res = _eliminate_variables(quantifiers, ccnf, config)
    #print("Eliminated!")

    return res

##############################################################################################
### TESTS
##############################################################################################

TEST_DIR = './Test_works/'

def test_renaming():
    _, _, clauses, quantifiers = read_qdimacs_from_file_unchecked(TEST_DIR + 'unsat/r_807')
    print('=' * 50)
    print("PRE")
    print(quantifiers)
    print(clauses)

    _rename_variables(quantifiers, clauses)

    print('=' * 50)
    print("POST")
    print(quantifiers)
    print(clauses)

def test_inf_solver():
    directory_sat = TEST_DIR + "sat"
    directory_unsat = TEST_DIR + "unsat"

    print('\n##################################\n\tTesting INF-Solver\n##################################')
    print('\nProcessing SAT ...')
    exclude = [] # b.q Killed --> No al usar el SAT solver
    for filename_sat in os.listdir(directory_sat):
        if filename_sat in exclude:
            continue
        print(f'--- Processing {filename_sat} ... ', flush=True)
        file_path = os.path.join(directory_sat, filename_sat)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        #set_trace()
        res = inf_solver(quantifiers, clauses, debugging=False)
        t1 = time()
        print('SAT' if res else 'UNSAT')
        print(f"Time: {t1 - t0 : .4f}")
        reset_debugging()
    """
    Con b.q sale 'Killed' en pantalla -> Falta de memoria y el SO mata el proceso -> No con el SAT solver
    Con los demás va bien
    """

    print('\nProcessing UNSAT ...')
    for filename_unsat in os.listdir(directory_unsat):
        print(f'--- Processing {filename_unsat} ... ', flush=True)
        file_path = os.path.join(directory_unsat, filename_unsat)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        res = inf_solver(quantifiers, clauses, debugging=False)
        t1 = time()
        print('SAT' if res else 'UNSAT')
        print(f"Time: {t1 - t0 : .4f}")
        reset_debugging()
    """
    Funciona con todos!
    """

def test_inf_with_difficult_instances():
    directory_sat = TEST_DIR + "sat"
    instance1 = directory_sat + "/r_100_80_11.qdimacs"
    instance2 = directory_sat + "/b.q"

    """
    print('\n##################################\n\tTesting Naive-Solver v1\n##################################')
    print("### Instance 1:", instance1)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    t0 = time()
    res = naive_solver_v1(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')
    
    print("### Instance 2:", instance2)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    t0 = time()
    res = naive_solver_v1(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')
    """

    """
    print('\n##################################\n\tTesting INF-Solver\n##################################')
    print("### Instance 1:", instance1)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    t0 = time()
    res = inf_solver(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')
    """

    #set_trace()
    
    print("### Instance 2:", instance2)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    t0 = time()
    res = inf_solver(quantifiers, clauses, check_sat=False)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')

def test_eliminate_first_with_problematic_instances():
    directory_unsat = TEST_DIR + "unsat"
    instance1 = directory_unsat + "/t1.q"
    instance2 = directory_unsat + "/t2.q"

    print('\n##################################\n\tTesting INF-Solver with Eliminate_First OFF\n##################################')
    print("### Instance 1:", instance1)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    set_trace()
    res = inf_solver(quantifiers, clauses)
    print('SAT' if res else 'UNSAT')

    print("### Instance 2:", instance2)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    set_trace()
    res = inf_solver(quantifiers, clauses)
    print('SAT' if res else 'UNSAT')

    print('\n##################################\n\tTesting INF-Solver with Eliminate_First ON\n##################################')
    print("### Instance 1:", instance1)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    set_trace()
    res = inf_solver(quantifiers, clauses, eliminate_first=True)
    print('SAT' if res else 'UNSAT')

    print("### Instance 2:", instance2)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    set_trace()
    res = inf_solver(quantifiers, clauses, eliminate_first=True)
    print('SAT' if res else 'UNSAT')

def test_preprocessor():
    """
    CONCLUSIÓN: no usamos ningún preprocesador.

    PySAT: está implementado para SAT. Hace operaciones con dicha presuposición, por lo que es incompatible con
        los unificadores universales de QBF.
    MAC: mismo razonamiento que con el anterior.
    Bica: es posible que sea utilizable. No obstante, es más complicado, requiere que la entrada esté
        en un fichero, el resultado también lo pone en un fichero, y sobre todo, con la configuración
        por defecto realiza la negación de la fórmula, que puede ser en sí mismo una operación muy costosa.
    """
    
    directory_unsat = TEST_DIR + "unsat"
    instance = directory_unsat + "/r_141"

    print('\n##################################\n\tTesting INF-Solver with Preprocessor\n##################################')
    print("### Instance:", instance)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance)
    res = inf_solver(quantifiers, clauses, eliminate_first=True)
    print('SAT' if res else 'UNSAT')

    print("### Instance: the same but with all existential variables and no preprocessor")
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance)
    quantifiers = [('e', vars) for (q, vars) in quantifiers]
    res = inf_solver(quantifiers, clauses, eliminate_first=True, preprocess=False)
    print('SAT' if res else 'UNSAT')


def read_nv_nc(file_path):
    with open(file_path) as f:
        for line in f:
            tokens = line.strip().split()
            if tokens[0] == 'p' and tokens[1] == 'cnf':
                return int(tokens[2]), int(tokens[3])
    print(f"PROBLEMATIC INSTANCE: {file_path}")

def test_generated():
    sys.setrecursionlimit(3000)

    directory = 'TestsGeneratedCombinationalEquivalence2017/klieber2017/'

    print('\n##################################\n\tTesting Generated 2017\n##################################')
    nvs, ncs = [], []
    instances_less_than = defaultdict(list)
    for filename in os.listdir(directory):
        #print(f"Processing {filename} ...")
        file_path = os.path.join(directory, filename)
        res = read_nv_nc(file_path)
        if res is None:
            continue
        nv, nc = res
        nvs.append(nv)
        ncs.append(nc)
        for limit in [600 + 100*i for i in range(9)]:
            if nv <= limit: #and nc <= limit:
                instances_less_than[limit].append(filename)
                break
        else: #nobreak
            instances_less_than[100000].append(filename)

    nvs, ncs = np.array(nvs), np.array(ncs)
    print(f"Maximum number of variables: {np.max(nvs)}")
    print(f"Minimum number of variables: {np.min(nvs)}")
    print(f"Mean number of variables:    {np.mean(nvs)}")
    print(f"Maximum number of clauses:   {np.max(ncs)}")
    print(f"Minimum number of clauses:   {np.min(ncs)}")
    print(f"Mean number of clauses:      {np.mean(ncs)}")

    for limit, instances in sorted(instances_less_than.items(), key=lambda li: li[0]):
        print(f"Number of instances with less than {limit} vars: {len(instances)}")

    for filename in [fn for limit in [600 + 100*i for i in range(5)] for fn in instances_less_than[limit]]:
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        #set_trace()
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        res = None # Inicializa res a None
        try:
            with time_limit(10): # Aquí aplicamos el límite de 60 segundos
                res = inf_solver(quantifiers, clauses, debugging=False)
            t1 = time()
            print('SAT' if res else 'UNSAT')
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad
        reset_debugging()

def test_qbfgallery2020():
    sys.setrecursionlimit(3000)
    directory = 'TestsQBFGallery2020/PCNF/'

    print('\n##################################\n\tTesting QBFGallery 2020\n##################################')
    nvs, ncs = [], []
    instances_less_than = defaultdict(list)
    for filename in os.listdir(directory):
        file_path = os.path.join(directory, filename)
        res = read_nv_nc(file_path)
        if res is None:
            continue
        nv, nc = res
        nvs.append(nv)
        ncs.append(nc)
        for limit in [1000 * i for i in range(1, 11)]:
            if nv <= limit and nc <= limit:
                instances_less_than[limit].append(filename)
                break
        else: #nobreak
            instances_less_than[100000].append(filename)

    nvs, ncs = np.array(nvs), np.array(ncs)
    print(f"Maximum number of variables: {np.max(nvs)}")
    print(f"Minimum number of variables: {np.min(nvs)}")
    print(f"Mean number of variables:    {np.mean(nvs)}")
    print(f"Maximum number of clauses:   {np.max(ncs)}")
    print(f"Minimum number of clauses:   {np.min(ncs)}")
    print(f"Mean number of clauses:      {np.mean(ncs)}")

    for limit, instances in sorted(instances_less_than.items(), key=lambda li: li[0]):
        print(f"Number of instances with less than {limit} vars and clauses: {len(instances)}")
    
    for filename in instances_less_than[1000]:
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        #set_trace()
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        res = None # Inicializa res a None
        try:
            with time_limit(10): # Aquí aplicamos el límite de 60 segundos
                res = inf_solver(quantifiers, clauses, debugging=True)
            t1 = time()
            print('SAT' if res else 'UNSAT')
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad
        reset_debugging()

def test_qbfgallery2023():
    sys.setrecursionlimit(3000)
    directory = 'TestsQBFGallery2023/qdimacs/'

    print('\n##################################\n\tTesting QBFGallery 2023\n##################################')
    nvs, ncs = [], []
    instances_less_than = defaultdict(list)
    for filename in os.listdir(directory):
        file_path = os.path.join(directory, filename)
        res = read_nv_nc(file_path)
        if res is None:
            continue
        nv, nc = res
        nvs.append(nv)
        ncs.append(nc)
        for limit in [1000 * i for i in range(1, 11)]:
            if nv <= limit and nc <= limit:
                instances_less_than[limit].append(filename)
                break
        else: #nobreak
            instances_less_than[100000].append(filename)

    nvs, ncs = np.array(nvs), np.array(ncs)
    print(f"Maximum number of variables: {np.max(nvs)}")
    print(f"Minimum number of variables: {np.min(nvs)}")
    print(f"Mean number of variables:    {np.mean(nvs)}")
    print(f"Maximum number of clauses:   {np.max(ncs)}")
    print(f"Minimum number of clauses:   {np.min(ncs)}")
    print(f"Mean number of clauses:      {np.mean(ncs)}")

    for limit, instances in sorted(instances_less_than.items(), key=lambda li: li[0]):
        print(f"Number of instances with less than {limit} vars and clauses: {len(instances)}")

    for filename in instances_less_than[1000]:
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        res = None # Inicializa res a None
        try:
            with time_limit(10): # Aquí aplicamos el límite de 60 segundos
                res = inf_solver(quantifiers, clauses, debugging=True)
            t1 = time()
            print('SAT' if res else 'UNSAT')
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad
        reset_debugging()

def test_integration():
    print("----------- TEST INTEGRATION ---------------")

    sys.setrecursionlimit(4000)
    directory = 'integration-tests/'
    
    #####################################
    print("\tInstances not even DepQBF")
    not_even_depqbf = [
        "15.adder2.qdimacs",
        "55.driverlog09_8.qdimacs",
        "40.bug10rr.qdimacs",
        "49.c1_BMC_p1_k8.qdimacs",
        "53.C499.blif_0.10_0.20_0_0_inp_exact.qdimacs",
        "56.driverlog10_7.qdimacs",
        "50.c3_BMC_p1_k256.qdimacs",
        "155.stmt27rrr.qdimacs"
    ]

    for filename in not_even_depqbf:
        file_path = os.path.join(directory, filename)
        nv, nc = read_nv_nc(file_path)
        print(f"{filename} - nv = {nv} - nc = {nc}")
    #####################################
    
    results = {
        '1.true.qdimacs': True,
        '10.SAT.qdimacs': True,
        '10.SAT.qdimacs_to_dimacs.cnf': True,
        '100.lights3_021_0_013.qdimacs': False,
        '101.mb3.qdimacs': False,
        '102.mb3_reduced.qdimacs': False,
        '103.miniTest78_reduced.qdimacs': False,
        '104.miniTestb267_reduced.qdimacs': False,
        '105.miniTestb267rr.qdimacs': True,
        '106.miniTestb267rr2.qdimacs': True,
        '107.miniTestb282_reduced.qdimacs': False,
        '109.mvs.qdimacs': False,
        '11.SAT.qdimacs': True,
        '110.mvsr.qdimacs': False,
        '111.mvsr3_reduced.qdimacs': True,
        '112.or_blocked.qdimacs': False,
        '113.or_hidden.qdimacs': False,
        '114.p5-5.pddl_planlen=2.qdimacs': False,
        '115.p10-1.pddl_planlen=4.qdimacs.txt': False,
        '116.p10-5.pddl_planlen=19.qdimacs': True,
        '117.partition.qdimacs': True,
        '118.partition2.qdimacs': True,
        '119.pec_adder_32bit_sat.qdimacs': True,
        '12.SAT.qdimacs': True,
        '120.pec_adder_32bit_sat_reduced.qdimacs': True,
        '121.pec_adder_sat.qdimacs': True,
        '122.pec_adder_unsat.mod.qdimacs': False,
        '123.pec_adder_unsat.prop.qdimacs': False,
        '124.pec_adder_unsat.qdimacs': False,
        '125.pec_adder_unsat.simp.qdimacs': False,
        '126.pec_adder_unsat_reduced.qdimacs': False,
        '127.pec_adder_unsat_reduced2.qdimacs': False,
        '128.pec_example_circuit_6_2_2_reduced.qdimacs': True,
        '129.projection_error2.qdimacs': True,
        '13.UNSAT.qdimacs': False,
        '130.propagation_sat.qdimacs': True,
        '131.rareqs_paper_example.qdimacs': False,
        '132.rf28rr.qdimacs': True,
        '133.rf_reduced.qdimacs': True,
        '134.s713_d4_s.qdimacs': True,
        '135.s1269_d2_s.qdimacs': True,
        '136.s5378_1_0.qdimacs': True,
        '137.s05378_PR_7_2.qdimacs.txt': True,
        '138.s15850_PR_5_90.qdimacs': False,
        '139.s38584_PR_1_2.qdimacs': True,
        '14.a2r.qdimacs': False,
        '140.segfault.qdimacs': True,
        '141.segfault2.qdimacs': True,
        '142.simple_sat.qdimacs': True,
        '143.simple_seperated.qdimacs': True,
        '144.sns53_reduced.qdimacs': True,
        '145.sns56rrr.qdimacs': True,
        '146.sorting_network_4_5_reduced.qdimacs': True,
        '147.sorting_network_4_5_rr.qdimacs': False,
        '148.sortnetsort5AEstepl003_reduced.qdimacs': False,
        '149.stmt5rr.qdimacs': True,
        '150.stmt7rr.qdimacs': True,
        '151.stmt21_4_5_reduced.qdimacs': False,
        '152.stmt21r4.qdimacs': True,
        '153.stmt21rr.qdimacs': True,
        '154.stmt27_149_224.qdimacs.txt': False,
        '156.test_implications.qdimacs': False,
        '157.test_sat.qdimacs': True,
        '158.test_unsat.qdimacs': False,
        '159.tmp-47850_reduced.qdimacs': True,
        '16.arbiter_bug2.qdimacs': False,
        '16.arbiter_bug2.qdimacs~': False,
        '17.arbiter_reduced.qdimacs': True,
        '18.asdf2.qdimacs': False,
        '19.asdf4_reduced.qdimacs': True,
        '2.SAT.dimacs': True,
        '20.asdf_reduced.qdimacs': True,
        '21.b17-4.qdimacs': False,
        '22.b17-4r.qdimacs': False,
        '23.biu.qdimacs': True,
        '24.biubug.qdimacs': True,
        '25.biu_manual.qdimacs': True,
        '26.blocks_reduced.qdimacs': True,
        '27.br.qdimacs': True,
        '28.br3_reduced.qdimacs': False,
        '29.brrr.qdimacs': True,
        '3.UNSAT.dimacs': False,
        '30.bug1.qdimacs': False,
        '31.bug3.qdimacs': False,
        '32.bug5.qdimacs': True,
        '33.bug6.qdimacs': True,
        '34.bug6_reduced.qdimacs': False,
        '35.bug6rr.qdimacs': True,
        '36.bug6rrmod.qdimacs': True,
        '37.bug7.qdimacs': False,
        '38.bug8.qdimacs': False,
        '39.bug9.qdimacs': True,
        '4.UNSAT.dimacs': False,
        '41.bug10rrr.qdimacs': False,
        '42.bug17.qdimacs': False,
        '43.bug_abort.qdimacs': True,
        '44.bug_diverge.qdimacs': True,
        '45.bug_diverge2.qdimacs': True,
        '46.bug_lights.qdimacs': True,
        '47.bug_refinement.qdimacs': False,
        '48.bug_refinement_reduced2.qdimacs': False,
        '5.UNSAT.dimacs': False,
        '51.dungeon_i15-m75-u10-v0.pddl_planlen=4.qdimacs': True,
        '52.c5_BMC_p1_k4.qdimacs': True,
        '54.constants_and_elimination.qdimacs': True,
        '57.dungeon_i25-m125-u3-v0.pddl_planlen=13.bloqqer.qdimacs': True,
        '58.dungeon_i25-m125-u3-v0.pddl_planlen=13.qdimacs': True,
        '59.dungeon_i25-m125-u3-v0.pddl_planlen=14.qdimacs': True,
        '6.SAT.dimacs': True,
        '60.eequery_query04_1344n.qdimacs': True,
        '61.eequery_query04_1344n.qdimacs.txt': True,
        '62.eequery_query04_1344nqdimacs_reduced.txt': False,
        '63.eequery_query04_1344n_reduced.qdimacs': True,
        '64.eer.qdimacs': False,
        '65.eerr.qdimacs': False,
        '66.empty_clause.qdimacs': False,
        '67.equal.qdimacs': True,
        '68.equal_hidden.qdimacs': False,
        '69.equality_hidden.qdimacs': False,
        '7.SAT.qdimacs': True,
        '7.SAT.qdimacs_to_dimacs.cnf': True,
        '70.err.qdimacs': True,
        '71.ev-pr-4x4-5-3-0-0-1-s.qdimacs': True,
        '72.ev-pr-4x4-7-3-0-0-1-s.qdimacs': True,
        '73.example.qdimacs': False,
        '74.false.qdimacs': False,
        '74.false.qdimacs~': False,
        '75.frrr.qdimacs': True,
        '76.fuzz.qdimacs': True,
        '76.fuzz1.qdimacs': False,
        '77.fuzz606.qdimacs': False,
        '78.fuzz1380_reduced.qdimacs': True,
        '79.fuzz7300.qdimacs': False,
        '8.SAT.qdimacs': True,
        '80.fuzz9716.qdimacs': False,
        '81.fuzz10825.qdimacs': False,
        '82.fuzz10825_reduced.qdimacs': False,
        '83.fuzz12668_reduced.qdimacs': True,
        '84.fuzz12891.qdimacs': False,
        '85.fuzz14807_reduced.qdimacs': False,
        '86.fuzz17061.qdimacs': True,
        '87.fuzz19494_reduced.qdimacs': False,
        '88.fuzz19959.qdimacs': True,
        '89.fuzz22644.qdimacs': True,
        '9.SAT.qdimacs': True,
        '90.fuzz23979_reduced.qdimacs': False,
        '91.fuzz24003_reduced.qdimacs': False,
        '92.fuzz24330.qdimacs': True,
        '93.fuzz25823.qdimacs': False,
        '94.illegal_dependence_conflict.qdimacs': False,
        '95.illegal_dependence_conflict2.qdimacs': False,
        '96.incomplete_or.qdimacs': True,
        '97.k_ph_n-16.qdimacs': True,
        '98.lights.qdimacs': False,
        '99.lights3_021_0_009.qdimacs': True,
    }

    for filename in results.keys():
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        
        # Al testear cached, hay que vaciarlo para cada instancia
        CCNF.clean_caches()

        t0 = time()
        res = None
        try:
            with time_limit(10): # Aquí aplicamos el límite de 60 segundos
                res = inf_solver(quantifiers, clauses, debugging=False)
            t1 = time()
            print(f"{'CORRECT' if res == results[filename] else 'INCORRECT'} {'SAT' if res else 'UNSAT'}")
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad
        reset_debugging()

def test_problematic_integration():
    directory = "integration-tests"
    problematic = {
        '158.test_unsat.qdimacs': False
    }

    for filename in problematic.keys():
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        
        t0 = time()
        res = None
        try:
            if filename.startswith('85'): set_trace()

            #with time_limit(10): # Aquí aplicamos el límite de 60 segundos
            res = inf_solver(quantifiers, clauses, debugging=False)
            
            t1 = time()
            print(f"{'CORRECT' if res == problematic[filename] else 'INCORRECT'} {'SAT' if res else 'UNSAT'}")
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad
        reset_debugging()

if __name__ == '__main__':

    config = {
        'debugging'                         : False,    # No es una variante a experimentar. A False para no printear innecesariamente
        'pre_simplify_tautologies'          : True,     # Hacerlo siempre
        'iterative'                         : True,     # Hacerlo siempre (eliminate_variables y simplify)

        'conjunction_direct_association'    : False,
        
        'elim_e_disj_conj'                  : False,
        'parallel_elim_e_conj2_disj'        : False,    # Solo testearlo si elim_e_disj_conj es menos eficiente (no esperable)
        
        'simplify'                          : False,    # Afecta a compactify, conjunction y disjunction
        
        'preprocessor'                      : False,
        
        'cached_nodes'                      : False,    # Afecta a create_node -> compactify, simplify, conjunction, disjunction
        'equals_with_is'                    : True,     # Solo si cached is True
        
        'absorb_with_prefixes'              : False,
        'disable_gc'                        : False,
        'check_sat'                         : False,
    
        'conjunction_parallel'              : False,
        'conjunction_parallel_lazy'         : True,     # Solo aplicable si conjunction_parallel is True

        'disjunction_parallel'              : False,
        'disjunction_parallel_conjs'        : False,    # Solo aplicable si disjunction_parallel is True
        'disjunction_parallel_disjs'        : False,    # Solo aplicable si disjunction_parallel is True
        
        'conjunction_cached_lru'            : False,    # Incompatible con parallel
        'disjunction_cached_lru'            : False,    # Incompatible con parallel
        
        'conjunction_cached_dicts'          : False,    # Excluyente con lru, es decir, los dos no pueden ser True
        'disjunction_cached_dicts'          : False,    # Excluyente con lru, es decir, los dos no pueden ser True

        'version_cached'                    : False,
        'version_cached_cleanup'            : None,     # Estos solo son posibles de realizar si version_cached is True
        'version_cached_memo_lru'           : None,     # nocleanup OBLIGATORIAMENTE
        'version_cached_memo_dicts'         : None,    # Este podemos combinarlo con cleanup y nocleanup
    }

    assert not config['debugging'], "Incorrect configuration! [1]"
    assert config['pre_simplify_tautologies'], "Incorrect configuration! [2]"
    assert config['iterative'], "Incorrect configuration! [3]" 
    assert not config['elim_e_disj_conj'] or not config['parallel_elim_e_conj2_disj'], "Incorrect configuration [4]"
    assert config['cached_nodes'] or not config['equals_with_is'], "Incorrect configuration! [5]"
    assert not config['equals_with_is'] or not config['conjunction_parallel'], "Incorrect configuration! [6]"
    assert not config['equals_with_is'] or not config['disjunction_parallel'], "Incorrect configuration! [7]"
    assert not config['disjunction_parallel'] or (config['disjunction_parallel_conjs'] or config['disjunction_parallel_disjs']), "Incorrect configuration! [8]"
    # Estos assert son innecesarios. Si _parallel está activo, se hará la llamada a dicha versión.
    # Eso sí, dentro de él, creará subprocesos con la función _serial_wrapper. Es decir, 
    # podemos decidir si en el subproceso usar memoización o no.
    #assert not config['conjunction_parallel'] or not config['conjunction_cached_lru'], "Incorrect configuration! [9]"
    #assert not config['conjunction_parallel'] or not config['conjunction_cached_dicts'], "Incorrect configuration! [10]"
    #assert not config['disjunction_parallel'] or not config['disjunction_cached_lru'], "Incorrect configuration! [11]"
    #assert not config['disjunction_parallel'] or not config['disjunction_cached_dicts'], "Incorrect configuration! [12]"
    assert not config['conjunction_cached_lru'] or not config['conjunction_cached_dicts'], "Incorrect configuration! [13]"
    assert not config['disjunction_cached_lru'] or not config['disjunction_cached_dicts'], "Incorrect configuration! [14]"
    assert not config['version_cached'], "Incorrect script (this is tuples) for set value cached version! [15]"
    
    #"""
    if len(sys.argv) != 2:
        print("ERROR: usage --> python3 qbf_inf_solver_tuples.py <name_instance in QDIMACS>", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    sys.setrecursionlimit(4000)

    file_path = sys.argv[1]
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
    print('SAT' if inf_solver(quantifiers, clauses, config) else 'UNSAT')
    #"""

    #test_renaming()
    #test_inf_solver()
    #test_inf_with_difficult_instances()
    #test_eliminate_first_with_problematic_instances()
    #test_preprocessor()
    # Nota: timeout 10s no es suficiente! --> Pero no es el timeout, llega un punto que la cantidad de nodos es demasiado grande
    #test_generated()
    # Nota: timeout 10s no es suficiente! --> Parece que alguna eliminación más podría llegar a hacer, pero el número de nodos es enorme
    #test_qbfgallery2020()
    # Nota: timeout 10s no es suficiente! --> Parece que alguna eliminación más podría llegar a hacer, pero el número de nodos es enorme
    #test_qbfgallery2023()
    #test_integration()
    #test_problematic_integration()
    #pass