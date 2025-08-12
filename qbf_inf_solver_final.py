# qbf_inf_solver.py

##############################################################################################
### IMPORTS ##################################################################################
from pdb import set_trace
from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
from compactify_final import compactify, conjunction, disjunction
import gc
from pysat.solvers import Solver
import sys

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


def _eliminate_variables(quantifiers: List[QBlock], ccnf: Union[Tuple, bool]) -> bool:
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

        # Simplificamos la fórmula
        if q == 'a':
            # INF formula (C-CNF + universal quantifier)
            psi = conjunction(ccnf[1], ccnf[2])
            ccnf = conjunction(psi, ccnf[3])
        else:
            # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
            psi = disjunction(ccnf[2], ccnf[1])
            ccnf = conjunction(psi, ccnf[3])

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    Function that receives the result of the parser and applies our QBF solver
    that takes advantage of the Inductive Normal Form.
    """
    # Si estamos tratando con una instancia de SAT, mejor llamar directamente a un SAT solver optimizado de PySAT
    if len(quantifiers) == 1 and quantifiers[0][0] == 'e':
        with Solver(bootstrap_with=clauses) as s:
            return s.solve()
    
    # Sabemos que no hay referencias circulares, por lo que desactivamos el garbage collector generacional
    # Por supuesto, el garbage collector con el counter de las referencias sigue trabajando
    gc.disable()

    _rename_variables(quantifiers, clauses)

    ccnf = compactify(clauses, quantifiers)

    return _eliminate_variables(quantifiers, ccnf)

##############################################################################################
### MAIN
##############################################################################################

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("ERROR: usage --> python3 qbf_inf_solver_tuples.py <name_instance in QDIMACS>", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    sys.setrecursionlimit(5000) # 100_000 for instances 138 (doesn't work even with 10_000) and 139

    file_path = sys.argv[1]
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
    print('SAT' if inf_solver(quantifiers, clauses) else 'UNSAT')
