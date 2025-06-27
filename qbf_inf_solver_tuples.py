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
    for (i, (_, vars)) in enumerate(quantifiers):
        for j, v in enumerate(vars):
            quantifiers[i][1][j] = new
            old2new[v] = new
            new += 1
    
    for i, clause in enumerate(clauses):
        for j, lit in enumerate(clause):
            if lit > 0:
                clauses[i][j] = old2new[lit]
            else:
                clauses[i][j] = -old2new[-lit]

DB_Max_v = None
DB_Total_nodes = None
DB_Nodes = None
DB_Size = None

def _eliminate_variables(quantifiers: List[QBlock], ccnf: Tuple | bool, 
                       eliminate_first = True, debugging = False, iterative = True) -> bool:
    if iterative:
        return _eliminate_variables_it(quantifiers, ccnf, eliminate_first, debugging)
    return _eliminate_variables_rec(quantifiers, ccnf, eliminate_first, debugging) 

def _eliminate_variables_rec(quantifiers: List[QBlock], ccnf: Tuple | bool, eliminate_first = True, debugging = False) -> bool:
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
    #set_trace()
    #"""
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
        psi = CCNF.conjunction(ccnf[1], ccnf[2], simplify=True)
        if debugging: print("Segunda conjunción...")
        psi = CCNF.conjunction(psi, ccnf[3], simplify=True)
    else:
        # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
        if debugging: print("Eliminating existential...")
        if eliminate_first:
            if debugging: print("Disyunción...")
            psi = CCNF.disjunction(ccnf[2], ccnf[1], simplify=True)
            if debugging: print("Conjunción...")
            psi = CCNF.conjunction(psi, ccnf[3], simplify=True)
        else:
            if debugging: print("Primera conjunción...")
            psi1 = CCNF.conjunction(ccnf[2], ccnf[3], simplify=True)
            if debugging: print("Segunda conjunción...")
            psi2 = CCNF.conjunction(ccnf[1], ccnf[3], simplify=True)
            if debugging: print("Disyunción...")
            psi = CCNF.disjunction(psi1, psi2, simplify=True)
    if debugging: print("Eliminated!")
    
    # Llamada recursiva para seguir eliminando variables
    return _eliminate_variables_rec(quantifiers, psi)

def _eliminate_variables_it(quantifiers: List[QBlock], ccnf: Tuple | bool, eliminate_first = True, debugging = False) -> bool:
    """
    TODO: microoptimización, una vez testeados las variantes, quedarnos con la más eficiente y quitar los flags y comprobaciones
    """
    while True:
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
        #set_trace()
        #"""
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
            psi = CCNF.conjunction(ccnf[1], ccnf[2], simplify=True)
            if debugging: print("Segunda conjunción...")
            ccnf = CCNF.conjunction(psi, ccnf[3], simplify=True)
        else:
            # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
            if debugging: print("Eliminating existential...")
            if eliminate_first:
                if debugging: print("Disyunción...")
                psi = CCNF.disjunction(ccnf[2], ccnf[1], simplify=True)
                if debugging: print("Conjunción...")
                ccnf = CCNF.conjunction(psi, ccnf[3], simplify=True)
            else:
                if debugging: print("Primera conjunción...")
                psi1 = CCNF.conjunction(ccnf[2], ccnf[3], simplify=True)
                if debugging: print("Segunda conjunción...")
                psi2 = CCNF.conjunction(ccnf[1], ccnf[3], simplify=True)
                if debugging: print("Disyunción...")
                ccnf = CCNF.disjunction(psi1, psi2, simplify=True)
        if debugging: print("Eliminated!")

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula, eliminate_first = True) -> bool:
    """
    Function that receives the result of the parser and applies our QBF solver
    that takes advantage of the Inductive Normal Form.
    """
    # Sabemos que no hay referencias circulares, por lo que desactivamos el garbage collector generacional
    # Por supuesto, el garbage collector con el counter de las referencias sigue trabajando
    gc.disable()

    # Si estamos tratando con una instancia de SAT, mejor llamar directamente a un SAT solver optimizado de PySAT
    if len(quantifiers) == 1 and quantifiers[0][0] == 'e':
        with Solver(bootstrap_with=clauses) as s:
            return s.solve()

    #print('Renaming variables...')
    _rename_variables(quantifiers, clauses)
    #print("Finished renaming!")
    
    #print('Compactifying formula...')
    #t0 = time()
    # But it doesn't seem to improve so much to put compactify with simplify...
    ccnf = compactify(clauses, False, True, False)
    #t1 = time()
    #print('Compactified!')
    #print(f"Time: {t1 - t0 : .4f} s")

    #print("Eliminating variables...")
    #gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_UNCOLLECTABLE)
    #gc.set_debug(0)
    res = _eliminate_variables(quantifiers, ccnf, eliminate_first=eliminate_first)
    #print("Eliminated!")

    global DB_Max_v
    global DB_Total_nodes
    global DB_Nodes
    global DB_Size

    DB_Max_v = DB_Total_nodes = DB_Nodes = DB_Size = None

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
        res = inf_solver(quantifiers, clauses)
        t1 = time()
        print('SAT' if res else 'UNSAT')
        print(f"Time: {t1 - t0 : .4f}")
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
        res = inf_solver(quantifiers, clauses)
        t1 = time()
        print('SAT' if res else 'UNSAT')
        print(f"Time: {t1 - t0 : .4f}")
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
    res = inf_solver(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')

def test_eliminate_first_with_problematic_instances():
    directory_sat = TEST_DIR + "unsat"
    instance1 = directory_sat + "/t1.q"
    instance2 = directory_sat + "/t2.q"

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



if __name__ == '__main__':
    #test_renaming()
    test_inf_solver()
    #test_inf_with_difficult_instances()
    #test_eliminate_first_with_problematic_instances()