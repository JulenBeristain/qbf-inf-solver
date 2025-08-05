# qbf_naive_solver.py

##############################################################################################
### IMPORTS ##################################################################################
from pysat.solvers import Solver
from pysat.formula import CNF, PYSAT_FALSE, Or # PYSAT_FALSE == Atom(False)
from itertools import product
import numpy as np
import os
from pdb import set_trace
import sys

from types_qbf import *
from qbf_parser import read_qdimacs_from_file_unchecked
from cnf_preprocessor import preprocess as preprocess_cnf

##############################################################################################
### AUXILIAR FUNCTIONS TO WORK WITH CNFs #####################################################
def _literal_is_satisfied(assignment: List[int], literal: int) -> bool:
    """
    Auxiliar function that checks if the literal is true given the current assignment.
    
    Args:
        assignment(List[int]): current assignment. It is a list of not repeated ints. If 
            v is in it, -v can not appear. (+ If it was ordered by absolute value, 
            binary search could be used).
            Furthermore, we know that either lit or -lit is contained.
        lit: literal that we want to check if is satisfied

    Returns: true iff the literal is in the assignment (with the same sign, important!).
    
    """
    for a in assignment:
        if a == literal: return True
        elif a == -literal: return False
    assert False, ("AN ASSIGNMENT THAT DOESN'T CONTAIN A LITERAL THAT WE ARE CHECKING SHOULD NEVER "
                  "HAPPEN! THERE IS NO FREE VARIABLE!")

def _clause_is_satisfied(assignment: List[int], clause: Clause) -> bool:
    """ Auxiliar function that checks if the clause is true given the current assignment. """
    return any( _literal_is_satisfied(assignment, l) for l in clause )

def _formula_is_satisfied(assignment: List[int], clauses: CNF_Formula):
    """ Auxiliar function that checks if the CNF formula is true given the current assignment. """
    return all( _clause_is_satisfied(assignment, c) for c in clauses )

##############################################################################################

def _simplified_clause(assignment: List[int], clause: Clause) -> Optional[Clause]:
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
##############################################################################################
def naive_solver_v1(quantifiers: List[QBlock], clauses: CNF_Formula, preprocess=False) -> bool:
    """
    """
    if not quantifiers: # Case of literal True
        return True
    
    if preprocess:
        if preprocess_cnf(clauses, quantifiers) is False:
            return False
        
    return naive_solver_v1_rec(quantifiers, clauses)

def naive_solver_v1_rec(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    PRE: quantifiers no está vacío.
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
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
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
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
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

def naive_solver_v1_2(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    """
    Version that calls to a SAT solver in the beginning of every recursive call. If the formula itself
    is false (equivalent to a single existential block with all the variables) then the quantified
    one is false too. Otherwise, it works exactly the same way as the original.

    For some problems it will find that it is not computable early, but in the case of satisfiable
    formulas an important overhead is added.
    """
    # TODO: este chequeo lo suyo es hacerlo una única vez en una función interfaz que llame a esta
    #       es para el caso del literal True
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

##############################################################################################
##############################################################################################

def naive_solver_v2(quantifiers: List[QBlock], clauses: CNF_Formula) -> bool:
    q, vs = quantifiers[0]

    if len(quantifiers) == 1:
        if q == 'e':
            # Check if clauses as a CNF can be passed or clausify() and .clauses have to be used 
            with Solver(bootstrap_with=clauses) as s:
                return s.solve()
        else: # q == 'a'
            with Solver(bootstrap_with=clauses) as s:
                num_solutions = len(s.enum_models())
                num_assignments = 2 ** len(vs)
                return num_solutions == num_assignments

    else:
        array_vs = np.array(vs)
        if q == 'e':
            # TODO
            # Alguna otra forma más eficiente para gestionar disyunciones con PySAT???
            total = PYSAT_FALSE
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                # Check if is implace or returns a copy --> I suppose inplace, so a copy of clauses is made
                clauses_ = clauses.copy() #deepcopy
                clauses_.simplified(assumption)

            # COMPROBAR SI ESTO ES SIQUIERA POSIBLE HACERLO
                total = Or(total, clauses_)
            total = CNF(from_clauses = total.clausify())
            return naive_solver_v2(quantifiers[1:], total)

        else: # q == 'a'
            total = CNF()
            # Pillar todas las permutaciones de 1 y -1 de longitud len(vs)
            for assignment in product([1, -1], repeat=len(vs)):
                assumption = np.array(assignment) * array_vs
                # Check if is implace or returns a copy --> I suppose inplace, so a copy of clauses is made
                clauses_ = clauses.copy() #deepcopy
                clauses_.simplified(assumption)

                # Check if a CNF object can be appended directly or if .clauses has to be accessed
                total.extend(clauses_)
            return naive_solver_v2(quantifiers[1:], total)

##############################################################################################
##############################################################################################

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
##############################################################################################
### TESTS ####################################################################################

def test(naive_solver, name):
    directory_sat = "Test_works/sat"
    directory_unsat = "Test_works/unsat"

    print(f'\n##################################\n\tTesting {name}\n##################################')
    print('\nProcessing SAT ...')
    for filename_sat in os.listdir(directory_sat):
        print(f'Processing {filename_sat} ...')
        file_path = os.path.join(directory_sat, filename_sat)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        assert naive_solver(quantifiers, clauses), f"SAT was not obtained with {filename_sat}!\n"
    

    print('\nProcessing UNSAT ...')
    for filename_unsat in os.listdir(directory_unsat):
        print(f'Processing {filename_unsat} ...')
        file_path = os.path.join(directory_unsat, filename_unsat)
        #if filename_unsat == 'ucnf0.qdimacs':
        #    set_trace()
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        assert not naive_solver(quantifiers, clauses), f"UNSAT was NOT obtained with {filename_unsat}!\n"

def test_mikel_problem():
    quantifiers = [('a', [1]), ('e', [2])]
    clauses = [[-1,2],[1,-2]]
    assert naive_solver_v1(quantifiers, clauses), 'Pues resulta que no es SAT!!!'
    print('Sí que es SAT!')

    quantifiers = [('e', [1]), ('a', [2])]
    clauses = [[-1,2],[1, -2]]
    assert not naive_solver_v1(quantifiers, clauses), 'Pues resulta que no es UNSAT!!!'
    print('Sí que es UNSAT!')

if __name__ == '__main__':
    #test(naive_solver_v1, 'v1')
    #test(naive_solver_v1_2, 'v1_2')
    #test(naive_solver_v3, 'v3')
    #test(naive_solver_v3_2, 'v3_2')
    # v3 es muchísimo más ineficiente que v1!!!
    # TODO: test v3 excluding SAT/r_100_80_11.qdimacs
    #test_mikel_problem()

    #"""
    if len(sys.argv) != 2:
        print("ERROR: usage --> python3 qbf_naive_solver.py <name_instance in QDIMACS>", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    file_path = sys.argv[1]
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
    print('SAT' if naive_solver_v1(quantifiers, clauses, preprocess=False) else 'UNSAT')
    #"""
