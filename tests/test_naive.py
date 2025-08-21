# test_naive.py

##############################################################################################
### IMPORTS ##################################################################################

import os
from src.qbf_parser import read_qdimacs_from_file_unchecked
from src.qbf_naive_solver import (
    naive_solver_v1,
    naive_solver_v1_2,
    naive_solver_v3,
    naive_solver_v3_2
)

# Note: only v1 is used and tested

##############################################################################################
### TESTS ####################################################################################

def test(naive_solver, name: str) -> None:
    directory_sat = "data/Test_works/sat"
    directory_unsat = "data/Test_works/unsat"

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

def test_particular_problem() -> None:
    quantifiers = [('a', [1]), ('e', [2])]
    clauses = [[-1,2],[1,-2]]
    assert naive_solver_v1(quantifiers, clauses), 'Pues resulta que no es SAT!!!'
    print('Sí que es SAT!')

    quantifiers = [('e', [1]), ('a', [2])]
    clauses = [[-1,2],[1, -2]]
    assert not naive_solver_v1(quantifiers, clauses), 'Pues resulta que no es UNSAT!!!'
    print('Sí que es UNSAT!')

##############################################################################################
### MAIN #####################################################################################

if __name__ == '__main__':
    test(naive_solver_v1, 'v1')
    #test(naive_solver_v1_2, 'v1_2')
    #test(naive_solver_v3, 'v3')
    #test(naive_solver_v3_2, 'v3_2')
    # v3 es muchísimo más ineficiente que v1!!!
    #test_particular_problem()
    pass