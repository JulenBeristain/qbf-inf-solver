# compare_naive_and_fni.py

# Script that reads the results of the Naive (without preprocessor) and FNI solvers and compares them.
# More specifically, it focuses on the instances where these two solvers differ: those that are solved
# by the Naive and not by FNI and viceversa. The information about these instances (name, number of
# variables, clauses, quantifier blocks, etc.) is printed to the stdout.

import csv

if __name__ == '__main__':
    naive_results_filename = '../Naive_benchmark_results.csv'
    fni_results_filename = '../FNI_benchmark_results.csv'
    
    with open(naive_results_filename, 'r', newline='') as f:
        reader = csv.DictReader(f)
        naive_results = [res for res in reader]

    with open(fni_results_filename, 'r', newline='') as f:
        reader = csv.DictReader(f)
        fni_results = {res['instance'] : res for res in reader}

    better_naive, better_fni = [], []

    for res in naive_results:
        instance = res['instance']
        naive_status = res['status']
        
        fni_res = fni_results[instance]
        fni_status = fni_res['status']

        if naive_status != 'CORRECT' and fni_status == 'CORRECT':
            #print(f'{instance} : Naive < FNI', end=' | ')
            #print(f"Num vars={res['Variables']} - Num clauses={res['Clauses']}")
            #print('-' * 80)
            better_fni.append(res)
        
        elif naive_status == 'CORRECT' and fni_status != 'CORRECT':
            #print(f'{instance} : Naive > FNI', end=' | ')
            #print(f"Num vars={res['Variables']} - Num clauses={res['Clauses']}")
            #print('-' * 80)
            better_naive.append(res)

    print('=' * 80)
    print("\tInstances where NAIVE is better:")
    for instance in better_naive:
        print('-' * 50)
        print(instance['instance'])
        print(f"Num_vars={instance['Variables']} - Num_clauses={instance['Clauses']}")
        print(f"Clause_size_mean={instance['Clause_SZ_Mean']}")
        print(f"Num_quantifier_blocks={instance['QBlocks']}")
        print('-' * 50)
    print('=' * 80)
    print("\tInstances where FNI is better:")
    for instance in better_fni:
        print('-' * 50)
        print(instance['instance'])
        print(f"Num_vars={instance['Variables']} - Num_clauses={instance['Clauses']}")
        print(f"Clause_size_mean={instance['Clause_SZ_Mean']}")
        print(f"Num_quantifier_blocks={instance['QBlocks']}")
        print('-' * 50)