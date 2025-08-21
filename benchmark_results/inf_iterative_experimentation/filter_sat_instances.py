# filter_sat_instances.py

# Script that filters SAT instances from the list of instances used in the iterative experimentation.
# For that, we check if it has a unique quantifier block (then, we have manually checked that the
# quantifier blocks of the resulting instances are indeed existential).

import csv

INSTANCES_ITER_EXP = [
    '10.SAT.qdimacs',
    '10.SAT.qdimacs_to_dimacs.cnf',
    '100.lights3_021_0_013.qdimacs',
    '101.mb3.qdimacs',
    '103.miniTest78_reduced.qdimacs',
    '104.miniTestb267_reduced.qdimacs',
    '107.miniTestb282_reduced.qdimacs',
    '109.mvs.qdimacs',
    '114.p5-5.pddl_planlen=2.qdimacs',
    '115.p10-1.pddl_planlen=4.qdimacs.txt',
    '116.p10-5.pddl_planlen=19.qdimacs',
    '119.pec_adder_32bit_sat.qdimacs',
    '12.SAT.qdimacs',
    '13.UNSAT.qdimacs',
    '134.s713_d4_s.qdimacs',
    '135.s1269_d2_s.qdimacs',
    '136.s5378_1_0.qdimacs',
    '137.s05378_PR_7_2.qdimacs.txt',
    '138.s15850_PR_5_90.qdimacs',
    '139.s38584_PR_1_2.qdimacs',
    '140.segfault.qdimacs',
    '148.sortnetsort5AEstepl003_reduced.qdimacs',
    '150.stmt7rr.qdimacs',
    '151.stmt21_4_5_reduced.qdimacs',
    '154.stmt27_149_224.qdimacs.txt',
    '155.stmt27rrr.qdimacs',
    '2.SAT.dimacs',
    '21.b17-4.qdimacs',
    '22.b17-4r.qdimacs',
    '23.biu.qdimacs',
    '24.biubug.qdimacs',
    '27.br.qdimacs',
    '3.UNSAT.dimacs',
    '37.bug7.qdimacs',
    '38.bug8.qdimacs',
    '39.bug9.qdimacs',
    '4.UNSAT.dimacs',
    '41.bug10rrr.qdimacs',
    '42.bug17.qdimacs',
    '5.UNSAT.dimacs',
    '51.dungeon_i15-m75-u10-v0.pddl_planlen=4.qdimacs',
    '52.c5_BMC_p1_k4.qdimacs',
    '57.dungeon_i25-m125-u3-v0.pddl_planlen=13.bloqqer.qdimacs',
    '58.dungeon_i25-m125-u3-v0.pddl_planlen=13.qdimacs',
    '59.dungeon_i25-m125-u3-v0.pddl_planlen=14.qdimacs',
    '6.SAT.dimacs',
    '60.eequery_query04_1344n.qdimacs',
    '61.eequery_query04_1344n.qdimacs.txt',
    '62.eequery_query04_1344nqdimacs_reduced.txt',
    '71.ev-pr-4x4-5-3-0-0-1-s.qdimacs',
    '72.ev-pr-4x4-7-3-0-0-1-s.qdimacs',
    '76.fuzz.qdimacs',
    '8.SAT.qdimacs',
    '9.SAT.qdimacs',
    '97.k_ph_n-16.qdimacs',
    '99.lights3_021_0_009.qdimacs',
]

if __name__ == '__main__':
    file_stats = '../DepQBF_benchmark_results.csv'
    with open(file_stats, 'r', newline='') as f:
        reader = csv.DictReader(f)
        is_sat = lambda row: (row['QBlocks'] == '1') and (row['instance'] in INSTANCES_ITER_EXP)
        sat_instances = [row['instance'] for row in reader if is_sat(row)]
    
    print('SAT_INSTANCES = [')
    for instance in sat_instances:
        print(f"\t'{instance}',")
    print(']')