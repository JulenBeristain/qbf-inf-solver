# instance_info_script.py

##############################################################################################
### IMPORTS ##################################################################################

import os
import csv
import statistics
from pdb import set_trace
from typing import Dict

from src.qbf_parser import read_qdimacs_from_file_unchecked


##############################################################################################
### OBTAIN INSTANCE INFORMATION ##############################################################

def get_instance_info(instance_path: str) -> Dict:
    """
    Function that returns the info of the given instance in a dict with the following data:

    * Number of variables, number of clauses
    * Size of clauses: media, minimum, maximum, median, standard deviation, 
    * Number of quantifier blocks and a summary of the types of quantifiers with the number
      of quantified variables in each block

    Args:
        instance_path (str): the path to the QBF instance in QDIMACS format
    
    Returns:
        Dict: the dictionary with the mentioned information about the instance
    """
    nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(instance_path)

    # nv, nc can be incorrect in the header
    nc = len(clauses)

    vars_in_clauses = set()
    for clause in clauses:
        for literal in clause:
            vars_in_clauses.add(abs(literal))
    vars_quantified = set()
    for _, vars in quantifiers:
        for var in vars:
            vars_quantified.add(var)
        
    exceptions = [
        '135.s1269_d2_s.qdimacs', # Only e 74 0, with none of the rest 73 vars quantified --> Interpreted as SAT instance, all existential
    ]
    instance_name = os.path.basename(instance_path)
    ignore = instance_name in exceptions
    assert ignore or not (vars_in_clauses - vars_quantified), "There is some variable(s) that are not quantified!!!"
    nv = len(vars_in_clauses)

    # Tamaño de cláusulas
    if nc == 0:
        mean = min_ = max_ = median = std_dev = 0
    else:
        lengths = list(map(len, clauses))
        mean = statistics.mean(lengths)
        min_ = min(lengths)
        max_ = max(lengths)
        median = statistics.median(lengths)
        std_dev = statistics.stdev(lengths) if len(lengths) > 1 else 0.0

    # Número de bloques de cuantificadores
    nb = len(quantifiers)
    
    # String con la información de los bloques de cuantificadores.
    # Formato: en-am-ek-al-... donde n,m,k y l son el número de variables en cada bloque existencial (e) o universal (a)
    # Ejemplo: quantifiers = [('e', [1,2,3]), ('a', [4,5]), ('e', [6])] --> e3-a2-e1 
    qstring = '-'.join( f'{q}{len(vars)}' for (q,vars) in quantifiers )

    return {
        'Variables': nv,
        'Clauses': nc,
        'Clause_SZ_Mean': mean,
        'Clause_SZ_Min': min_,
        'Clause_SZ_Max': max_,
        'Clause_SZ_Median': median,
        'Clause_SZ_StdDev': std_dev,
        'QBlocks': nb,
        'QString': qstring,
    }
    
    
##############################################################################################
### MAIN #####################################################################################

if __name__ == "__main__":
    # Note: if the directory in the server is different change this
    instance_dir = "data/integration-tests"
    instances = [os.path.join(instance_dir, f) for f in os.listdir(instance_dir)]

    all_infos = [{'Instance': os.path.basename(instance_path), **get_instance_info(instance_path)}
                 for instance_path in sorted(instances)]
        
    # Save results to a CSV file
    output_csv_file = "benchmark_results/instance_information.csv"
    keys = all_infos[0].keys()
    with open(output_csv_file, 'w', newline='') as output_file:
        dict_writer = csv.DictWriter(output_file, fieldnames=keys)
        dict_writer.writeheader()
        dict_writer.writerows(all_infos)
    print(f"Instance information saved to {output_csv_file}")
    