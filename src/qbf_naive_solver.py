# qbf_naive_solver.py

##############################################################################################
### IMPORTS ##################################################################################

from pysat.solvers import Solver
from pysat.formula import CNF
from itertools import product
import numpy as np
from pdb import set_trace
import sys

from .types_qbf import *
from .qbf_parser import read_qdimacs_from_file_unchecked
from .cnf_preprocessor import preprocess as preprocess_cnf

##############################################################################################
### AUXILIAR FUNCTIONS TO WORK WITH CNFs #####################################################

##############################################################################################
### SATISFACTION OF CNFs #####################################################################

def _literal_is_satisfied(assignment: List[int], literal: int) -> bool:
    """
    Auxiliar function that checks if the literal is true given the current assignment.
    
    Args:
        assignment (List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used). If v is in assignment, then True has 
            been assigned to the variable v. If -v is in assignment, False has been assigned to
            the variable v.
            Furthermore, we know that either lit or -lit is contained.
        lit (int): literal that we want to check if is satisfied.

    Returns: 
        bool: true iff the literal is in the assignment (with the same sign, important!).
    """
    for a in assignment:
        if a == literal: return True
        elif a == -literal: return False
    assert False, ("AN ASSIGNMENT THAT DOESN'T CONTAIN A LITERAL THAT WE ARE CHECKING SHOULD NEVER "
                  "HAPPEN! THERE IS NO FREE VARIABLE!")

def _clause_is_satisfied(assignment: List[int], clause: Clause) -> bool:
    """
    Auxiliar function that checks if the clause is true given the current assignment.
    
    Args:
        assignment (List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used). If v is in assignment, then True has 
            been assigned to the variable v. If -v is in assignment, False has been assigned to
            the variable v.
        clause (Clause): clause that we want to check if is satisfied.

    Returns: 
        bool: true iff anyone of the literals in the clause is satisfied given the assignment.
    """
    return any( _literal_is_satisfied(assignment, l) for l in clause )

def _formula_is_satisfied(assignment: List[int], clauses: CNF_Formula):
    """
    Auxiliar function that checks if the CNF formula is true given the current assignment.
   
    Args:
        assignment (List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used). If v is in assignment, then True has 
            been assigned to the variable v. If -v is in assignment, False has been assigned to
            the variable v.
        clauses (CNF_Formula): CNF formula that we want to check if is satisfied.

    Returns: 
        bool: true iff all the clauses are satisfied given the assignment.
    """
    return all( _clause_is_satisfied(assignment, c) for c in clauses )

##############################################################################################
### SIMPLIFICATION OF CNFs #####################################################

def _simplified_clause(assignment: List[int], clause: Clause) -> Optional[Clause]:
    """
    Auxiliar function that simplifies the clause given the current assignment. Literals that
    become False given the assignment are removed. If some literal is satisfied, None is returned
    to signal that the clause is satisfied and so it has to be removed. Otherwise, a new
    simplified clause is created, which only contains literals whose variables have not received
    an assignment yet.
   
    Args:
        assignment (List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used). If v is in assignment, then True has 
            been assigned to the variable v. If -v is in assignment, False has been assigned to
            the variable v.
        clause (Clause): clause that we want to simplify.

    Returns: 
        Optional[Clause]: None if any literal of clause becomes True with the assignment.
            Otherwise, the same clause but after the literals that become False have been filtered.
    """
    clause_ = []
    for lit in clause:
        for a in assignment:
            if a == lit: 
                # If true literal, then the clause is True too, so it will be simplified
                return None
            elif a == -lit:
                # Ignore false literal
                break
        else: # nobreak
            # Not assigned literal yet
            clause_.append(lit)
    
    return clause_

def _simplified_formula(assignment: List[int], clauses: CNF_Formula) -> Optional[CNF_Formula]:
    """
    Auxiliar function that simplifies the CNF formula given the current assignment. Every clause
    is simplified given the assignment. Satisfied clauses are removed. Literals that become False
    are deleted too. If some clause happens to be empty, then it is equivalent to False and the 
    entire formula would be False, so None is returned.
   
    Args:
        assignment (List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used). If v is in assignment, then True has 
            been assigned to the variable v. If -v is in assignment, False has been assigned to
            the variable v.
        clauses (CNF_Formula): CNF formula that we want to simplify.

    Returns: 
        Optional[CNF_Formula]: None if any clause becomes empty with the assignment.
            Otherwise, the same CNF formula filtering satisfied clauses and removing insatisfied literals.
    """
    clauses_ = []
    for clause in clauses:
        clause_ = _simplified_clause(assignment, clause)
        if clause_ is None:
            # Fulfilled clause
            continue
        if len(clause_) == 0:
            # False assignment
            return None
        clauses_.append(clause_)
    return clauses_

##############################################################################################
### NAIVE SOLVER #############################################################################

def naive_solver_v1(quantifiers: List[QBlock], clauses: CNF_Formula, preprocess=False) -> bool:
    """
    Function that solves a QBF instance with a naive algorithm. This version does recursion by
    blocks of quantified variables, not variable by variable, from left to right (from the outermost
    block to the innermost). In each call, it iterates over all possible assignments for the variables
    in the outermost block, and simplifies the CNF formula that it has received as the input (but 
    that formula is saved, in case more recursive calls are needed). Depending on the type of the 
    quantification of the block, we have early returns: if its universal and some assignment is False,
    we return directly False; if its existential and some assignment is True, we return directly True.
    I.e., we perform an AND of the recursive problems with all the possible assignments in the case of
    universal blocks, and an OR with the existential blocks. When only one block is left, if it is
    existential, we directly call to a SAT solver. If it is universal, we check if every assignment 
    is valid.

    This is an interface function that checks if there are no (quantified) variables, in which case
    we are facing the True literal. It also decides to apply the preprocessor of CNF matrices of
    QBF instances.
   
    Args:
        quantifiers (List[QBlock]): list of blocks of quantifiers; i.e., 2-tuples ('e'|'a', [vars]).
        clauses (CNF_Formula): CNF formula that we want to simplify.
        preprocess (bool): flag that determines if the preprocessor of CNFs is going to be used.

    Returns: 
        bool: true iff the QBF instance composed by quantifiers and clauses is satisfiable (equivalent to True).
    """
    if not quantifiers: # Case of literal True
        return True
    
    if preprocess:
        if preprocess_cnf(clauses, quantifiers) is False:
            return False
        
    return naive_solver_v1_rec(quantifiers, clauses)

def naive_solver_v1_rec(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    The worker recursive function for the version v1 of the Naive QBF solver.

    Precondition: quantifiers no está vacío.
    """
    q, vs = quantifiers[0]
    array_vs = np.array(vs) # Sorting vs by absolute valuecould be helpfull 
                            # in _literal_is_satisfied to enable binary search

    if len(quantifiers) == 1:
        if q == 'e':
            with Solver(bootstrap_with=clauses) as s:
                return s.solve()
        else: # q == 'a'
            # Not all models have to be found. Finding a single assignment that does not fulfill the
            # formula is enough.
            #with Solver(bootstrap_with=clauses) as s:
            #    num_solutions = len(s.enum_models())
            #    num_assignments = 2 ** len(vs)
            #    return num_solutions == num_assignments
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                if not _formula_is_satisfied(assumption, clauses):
                    return False
            return True

    else:
        quantifiers_ = quantifiers[1:]
        
        if q == 'e':
            # All permutations of 1 and -1 of length len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                clauses_ = _simplified_formula(assumption, clauses)
                if clauses_ is None:
                    # False assignment
                    continue
                
                if naive_solver_v1_rec(quantifiers_, clauses_):
                    return True
            return False

        else: # q == 'a'
            # All permutations of 1 and -1 of length len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                clauses_ = _simplified_formula(assumption, clauses)
                if clauses_ is None:
                    # False assignment
                    return False

                if not naive_solver_v1_rec(quantifiers_, clauses_):
                    return False
            return True

##############################################################################################
### MORE NAIVE SOLVERS #######################################################################
##############################################################################################

# Note: only the v1 of Naive solvers has been used in the experimentation phase of the project.
#   This following versions have not been thoroughly tested, they might contain errors of 
#   implementation. Furthermore, they need to be split in a interface and worker pair of functions
#   to check if quantifiers is not empty only once, and to give the option of using the preprocessor.

def naive_solver_v1_2(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    Version that calls to a SAT solver in the beginning of every recursive call. If the matrix
    is false (equivalent to a single existential block with all the variables or a SAT instance)
    then the quantified one is false too. Otherwise, it works exactly the same way as v1.

    For some problems it will find that it is not computable early, but in the case of satisfiable
    formulas an important overhead is added.
    """
    # TODO: este chequeo lo suyo es hacerlo una única vez en una función interfaz que llame a esta
    #       es para el caso del literal True, como en v1
    if not quantifiers:
        return True

    with Solver(bootstrap_with=clauses) as s:
        if not s.solve(): return False

    q, vs = quantifiers[0]
    array_vs = np.array(vs) # Sorting vs by absolute valuecould be helpfull 
                            # in _literal_is_satisfied to enable binary search

    if len(quantifiers) == 1:
        if q == 'e':
            # Already checked that a solution to clauses is found
            return True

        else: # q == 'a'
            # Not all models have to be found. Finding a single assignment that does not fulfill the
            # formula is enough.
            #with Solver(bootstrap_with=clauses) as s:
            #    num_solutions = len(s.enum_models())
            #    num_assignments = 2 ** len(vs)
            #    return num_solutions == num_assignments
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                if not _formula_is_satisfied(assumption, clauses):
                    return False
            return True

    else:
        quantifiers_ = quantifiers[1:]
        
        if q == 'e':
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                clauses_ = _simplified_formula(assumption, clauses)
                if clauses_ is None:
                    # False assignment
                    continue
                
                if naive_solver_v1(quantifiers_, clauses_):
                    return True
            return False

        else: # q == 'a'
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                clauses_ = _simplified_formula(assumption, clauses)
                if clauses_ is None:
                    # False assignment
                    return False

                if not naive_solver_v1(quantifiers_, clauses_):
                    return False
            return True

# Note: another version v2 was discarded, that is why the following ones are numbered with 3.

##############################################################################################
### V3 RECURSION PER VARIABLES ###############################################################

def naive_solver_v3(quantifiers: List[QBlock], clauses: CNF) -> bool:
    """
    Version that makes recursion not per block, like v1, but per variable.
    """
    # TODO: este chequeo lo suyo es hacerlo una única vez en una función interfaz que llame a esta
    #       es para el caso del literal True
    if not quantifiers:
        return True

    if clauses is None:
        return False  # At one point, in _simplified_clauses(...) [] in clauses_ was found

    q, vs = quantifiers[0]
    if len(quantifiers) == 1 and not vs:
        # All variables have been assigned. The formula is either true or false
        if len(clauses) == 0: return True
        assert False, "THERE SHOULD NOT BE ANY FREE VARIABLE!!!"
    
    quantifiers_ = quantifiers[1:]
    if not vs:
        # Block already was processed and there are remaining blocks
        return naive_solver_v3(quantifiers_, clauses)
    # There are still variables to process. We pick the first one, like we do with blocks
    v, vs_ = vs[0], vs[1:]
    quantifiers_ = [(q, vs_)] + quantifiers_
    # Two options. We assign it True or False
    clauses_ = _simplified_formula([v], clauses)
    res_ = naive_solver_v3(quantifiers_, clauses_)
    
    if q == 'e':
        if res_: return True
        # If the True assignment was not valid, we try with False
        clauses_ = _simplified_formula([-v], clauses)
        return naive_solver_v3(quantifiers_, clauses_)
    if q == 'a':
        if not res_: return False
        # If the True assignment was valid, we have to check with False too
        clauses_ = _simplified_formula([-v], clauses)
        return naive_solver_v3(quantifiers_, clauses_)

def naive_solver_v3_2(quantifiers: List[QBlock], clauses: CNF) -> bool:
    """
    Version that makes recursion not per block, like v1, but per variable.

    Additionally, this version calls to a SAT solver in the beginning of every recursive call. If the 
    formula itself is false (equivalent to a single existential block with all the variables) then the 
    quantified one is false too. Otherwise, it works exactly the same way as the original.

    For some problems it will find that it is not computable early, but in the case of satisfiable
    formulas an important overhead is added.
    """
    # TODO: este chequeo lo suyo es hacerlo una única vez en una función interfaz que llame a esta
    #       es para el caso del literal True
    if not quantifiers:
        return True

    if clauses is None:
        return False  # At one point, in _simplified_clauses(...) [] in clauses_ was found

    with Solver(bootstrap_with=clauses) as s:
        if not s.solve(): return False

    q, vs = quantifiers[0]
    if len(quantifiers) == 1 and not vs:
        # All variables have been assigned. The formula is either true or false
        if len(clauses) == 0: return True
        assert False, "THERE SHOULD NOT BE ANY FREE VARIABLE!!!"
    
    quantifiers_ = quantifiers[1:]
    if not vs:
        # Block already was processed and there are remaining blocks
        return naive_solver_v3(quantifiers_, clauses)
    # There are still variables to process. We pick the first one, like we do with blocks
    v, vs_ = vs[0], vs[1:]
    quantifiers_ = [(q, vs_)] + quantifiers_
    # Two options. We assign it True or False
    clauses_ = _simplified_formula([v], clauses)
    res_ = naive_solver_v3(quantifiers_, clauses_)
    
    if q == 'e':
        if res_: return True
        # If the True assignment was not valid, we try with False
        clauses_ = _simplified_formula([-v], clauses)
        return naive_solver_v3(quantifiers_, clauses_)
    if q == 'a':
        if not res_: return False
        # If the True assignment was valid, we have to check with False too
        clauses_ = _simplified_formula([-v], clauses)
        return naive_solver_v3(quantifiers_, clauses_)

##############################################################################################
### MAIN #####################################################################################

if __name__ == '__main__':
    
    if len(sys.argv) != 2:
        print("ERROR: usage --> python3 qbf_naive_solver.py <name_instance in QDIMACS>", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    file_path = sys.argv[1]
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
    print('SAT' if naive_solver_v1(quantifiers, clauses, preprocess=False) else 'UNSAT')

