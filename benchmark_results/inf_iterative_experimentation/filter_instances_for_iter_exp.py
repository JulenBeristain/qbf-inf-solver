# filter_instances_for_iter_exp.py

# Script that filters instances from test-integration following these criteria:
# * Avoid instances that DepQBF can not handle
# * Avoid instances that are too small (less than 100 variables and 100 clauses)
# * Include instances that Naive can not handle + the rest (decent size)

import csv

if __name__ == '__main__':
    
    instances = None
    
    with open('../DepQBF_benchmark_results.csv', 'r', newline='') as f:
        reader = csv.DictReader(f)
        instances = [ row['instance'] for row in reader if row['status'] != 'TIMEOUT' ]

    with open('../Naive_benchmark_results.csv', 'r', newline='') as f:
        reader = csv.DictReader(f)
        for row in reader:
            difficult_for_naive = row['status'] == 'TIMEOUT'
            enough_size = (int(row['Variables']) >= 100 or int(row['Clauses']) >= 100)
            if not (difficult_for_naive or enough_size):
                instances.remove(row['instance'])

    print(f'Number of instances: {len(instances)}')

    print('[')
    for i in instances:
        print(f"\t'{i}',")
    print(']')