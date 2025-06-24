# qbf_inf_solver.py

##############################################################################################
### IMPORTS ##################################################################################
import os
from pdb import set_trace
from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
from compactify import C_CNF_Tree, compactify
from qbf_naive_solver import naive_solver_v1
from time import time
import gc
import objgraph

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


def _eliminate_variables(quantifiers: List[QBlock], ccnf: C_CNF_Tree) -> bool:
    if ccnf.is_true(): return True
    if ccnf.is_false(): return False
    
    assert len(quantifiers) > 0, "NOS HEMOS QUEDADO SIN CUANTIFICADORES PERO LA FÓRMULA NO SE HA SIMPLIFICADO A TRUE O FALSE!!!"
    q = quantifiers[-1][0]
    assert q == 'a' or q == 'e', "CUANTIFICADOR DESCONOCIDO DETECTADO"

    # Nos quitamos la variable
    last_block_variables = quantifiers[-1][1]
    last_block_variables.pop()
    if not last_block_variables:
        quantifiers.pop()

    # Imprimimos la información antes de simplificar la fórmula
    #set_trace()
    #print("-" * 50)
    #print(f"Max_v = {ccnf.v}")
    #print(f"Depth = {ccnf.depth()}")
    #print(f"Max_nodes = {ccnf.max_nodes()}")
    #print(f"Actual_nodes = {ccnf.nodes()}")
    #print(f"Total_created_nodes = {C_CNF_Tree.num_nodes_created()}")
    #print(f"Size = {ccnf.size()}")
    #objgraph.show_most_common_types()
    #print("-" * 50, flush=True)

    # Simplificamos la fórmula
    if q == 'a':
        # INF formula (C-CNF + universal quantifier)
        #print("Eliminating universal...")
        #print("Primera conjunción...")
        psi = ccnf.negative.conjunction(ccnf.positive)
        #print("Segunda conjunción...")
        psi = psi.conjunction(ccnf.absent)
    else:
        # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
        #print("Eliminating existential...")
        #print("Primera conjunción...")
        psi1 = ccnf.positive.conjunction(ccnf.absent)
        #print("Segunda conjunción...")
        psi2 = ccnf.negative.conjunction(ccnf.absent)
        #print("Disyunción...")
        psi = psi1.disjunction(psi2)
    #print("Eliminated!")
    
    # Llamada recursiva para seguir eliminando variables
    return _eliminate_variables(quantifiers, psi)

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    Function that receives the result of the parser and applies our QBF solver
    that takes advantage of the Inductive Normal Form.
    """
    #print('Renaming variables...')
    _rename_variables(quantifiers, clauses)
    #print("Finished renaming!")
    
    #print('Compactifying formula...')
    ccnf = compactify(clauses, False)
    #print('Compactified!')

    #print("Eliminating variables...")
    #gc.set_debug(gc.DEBUG_STATS | gc.DEBUG_COLLECTABLE | gc.DEBUG_UNCOLLECTABLE)
    #gc.set_debug(0)
    res = _eliminate_variables(quantifiers, ccnf)
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
    exclude = ['r_100_80_11.qdimacs', 'b.q'] # Tarda bastante
    for filename_sat in os.listdir(directory_sat):
        if filename_sat in exclude:
            continue
        print(f'--- Processing {filename_sat} ... ', end='', flush=True)
        file_path = os.path.join(directory_sat, filename_sat)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        #assert inf_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
        t0 = time()
        res = inf_solver(quantifiers, clauses)
        t1 = time()
        print('SAT' if res else 'UNSAT')
        print(f"Time: {t1 - t0 : .4f}")
    """
    Con stmt24_7_8.qdimacs funciona, pero tarda un tiempo no despreciable (1 min aprox)
    Con r_100_80_11.qdimacs sale 'Killed' en pantalla -> Falta de memoria y el SO mata el proceso
    Con b.q sale 'Killed' en pantalla -> Falta de memoria y el SO mata el proceso
    Con los demás va bien
    """

    print('\nProcessing UNSAT ...')
    for filename_unsat in os.listdir(directory_unsat):
        print(f'--- Processing {filename_unsat} ... ', end='', flush=True)
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

def test_inf_with_diffucult_instances():
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
    
    print('\n##################################\n\tTesting INF-Solver\n##################################')
    print("### Instance 1:", instance1)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance1)
    t0 = time()
    res = inf_solver(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')

    print("### Instance 2:", instance2)
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance2)
    t0 = time()
    res = inf_solver(quantifiers, clauses)
    t1 = time()
    print('SAT' if res else 'UNSAT')
    print(f'Tiempo: {t1 - t0 : .4f} s')

if __name__ == '__main__':
    #test_renaming()
    test_inf_solver()
    #test_inf_with_diffucult_instances()