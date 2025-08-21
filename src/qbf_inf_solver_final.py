# qbf_inf_solver_final.py

##############################################################################################
### IMPORTS ##################################################################################

from pdb import set_trace
import gc
from pysat.solvers import Solver
import sys

from .cnf_preprocessor import rename_variables
from .types_qbf import *
from .qbf_parser import read_qdimacs_from_file_unchecked
from .regularize_final import regularize, conjunction, disjunction

##############################################################################################
### SOLVER USING INDUCTIVE NORMAL FORM
##############################################################################################

##############################################################################################
### ELIMINATION OF VARIABLES #################################################################

def _eliminate_variables(quantifiers: List[QBlock], rcnf: Union[Tuple, bool]) -> bool:
    """
    Function that eliminates quantified blocks, one variable at a time, until the formula is simplified to
    True or False. It uses conjunction and disjunction operations with subtrees in RCNF of the formula,
    depending on the quantifier of the variable that is eliminated in each step.

    The final version is iterative.

    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        rcnf (Union[Tuple, bool]): the matrix in RCNF of the QBF formula.
        
    Returns:
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    while True:
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

        # Simplify formula
        if q == 'a':
            # INF formula (C-CNF + universal quantifier)
            psi = conjunction(rcnf[1], rcnf[2])
            rcnf = conjunction(psi, rcnf[3])
        else:
            # No INF (C-CNF + existential quantifier), but it is PRENEX and the formula is compact
            psi = disjunction(rcnf[2], rcnf[1])
            rcnf = conjunction(psi, rcnf[3])

##############################################################################################
### INF SOLVER ###############################################################################

def inf_solver(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    Function that solves a QBF instance with our algorithm that takes advantage of the operations
    that are possible with quantified formulas in Inductive Normal Form, or alternatively (if the
    innermost variable is existential), formulas in prenex normal form with the matrix in RCNF. The 
    two main steps are:
    
    1. Convert the matrix in CNF of the original formula to RCNF.
    2. Perform the elimination of variables using boolean operations with the subtrees of the matrix
        in RCNF until it simplifies to True or False.
   
    A previous renaming of the variables might be needed if the variables were not ordered in 
    the blocks of quantifiers.

    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        clauses (CNF_Formula): CNF formula that we want to simplify.
        
    Returns: 
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    # If we have a SAT instance, it is better to call to a SAT solver of PySAT
    if len(quantifiers) == 1 and quantifiers[0][0] == 'e':
        with Solver(bootstrap_with=clauses) as s:
            return s.solve()
    
    # We know that there are no circular references, so we can turn off the generational garbage collection
    # Of course, the reference counting garbage collector keeps on working
    gc.disable()

    rename_variables(quantifiers, clauses)

    rcnf = regularize(clauses, quantifiers)

    return _eliminate_variables(quantifiers, rcnf)

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

    sys.setrecursionlimit(5000) # 100_000 for instances 138 (doesn't work even with 10_000) and 139
    print('SAT' if inf_solver(quantifiers, clauses) else 'UNSAT')
