# test_inf.py

##############################################################################################
### IMPORTS ##################################################################################

import os
from time import time
from sys import setrecursionlimit

from src.types_qbf import *
from src.qbf_parser import read_qdimacs_from_file_unchecked

from src.qbf_inf_solver_final import inf_solver
from src.regularize_final import clean_caches

# Note: in this tests we execute the final version of the INF solver over the majority of 
#   the integration tests (instances that DepQBF doesn't resolve fast are not considered)
#   with a small timeout of 10 seconds. We also use this script to test three last modifications:
#
#   * Complete the cnf_preprocessor to check the polarity variables more than once, since
#     we have realized that polarity and unit-propagation can generate more variables with
#     unique polarization.
#   * Use the complete absorbtion preprocessing of CNFs, because we only tested with 
#     prefixes initially.
#   * Trying to clean the nodes even if we have nested tuples

##############################################################################################
### TIMEOUT ##################################################################################

import signal
from contextlib import contextmanager

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
### READ NUM_VARS AND NUM_CLAUSES FROM FILE ##################################################

def read_nv_nc(file_path):
    with open(file_path) as f:
        for line in f:
            tokens = line.strip().split()
            if tokens[0] == 'p' and tokens[1] == 'cnf':
                return int(tokens[2]), int(tokens[3])
    print(f"PROBLEMATIC INSTANCE: {file_path}")

##############################################################################################
### TESTS
##############################################################################################

def test_integration(timeout: int) -> None:
    print("----------- TEST INTEGRATION ---------------")
    
    setrecursionlimit(5000)

    directory = 'data/integration-tests/'
    
    results = {
        '1.true.qdimacs': True,
        '10.SAT.qdimacs': True,
        '10.SAT.qdimacs_to_dimacs.cnf': True,
        '100.lights3_021_0_013.qdimacs': False,
        '101.mb3.qdimacs': False,
        '102.mb3_reduced.qdimacs': False,
        '103.miniTest78_reduced.qdimacs': False,
        '104.miniTestb267_reduced.qdimacs': False,
        '105.miniTestb267rr.qdimacs': True,
        '106.miniTestb267rr2.qdimacs': True,
        '107.miniTestb282_reduced.qdimacs': False,
        '109.mvs.qdimacs': False,
        '11.SAT.qdimacs': True,
        '110.mvsr.qdimacs': False,
        '111.mvsr3_reduced.qdimacs': True,
        '112.or_blocked.qdimacs': False,
        '113.or_hidden.qdimacs': False,
        '114.p5-5.pddl_planlen=2.qdimacs': False,
        '115.p10-1.pddl_planlen=4.qdimacs.txt': False,
        '116.p10-5.pddl_planlen=19.qdimacs': True,
        '117.partition.qdimacs': True,
        '118.partition2.qdimacs': True,
        '119.pec_adder_32bit_sat.qdimacs': True,
        '12.SAT.qdimacs': True,
        '120.pec_adder_32bit_sat_reduced.qdimacs': True,
        '121.pec_adder_sat.qdimacs': True,
        '122.pec_adder_unsat.mod.qdimacs': False,
        '123.pec_adder_unsat.prop.qdimacs': False,
        '124.pec_adder_unsat.qdimacs': False,
        '125.pec_adder_unsat.simp.qdimacs': False,
        '126.pec_adder_unsat_reduced.qdimacs': False,
        '127.pec_adder_unsat_reduced2.qdimacs': False,
        '128.pec_example_circuit_6_2_2_reduced.qdimacs': True,
        '129.projection_error2.qdimacs': True,
        '13.UNSAT.qdimacs': False,
        '130.propagation_sat.qdimacs': True,
        '131.rareqs_paper_example.qdimacs': False,
        '132.rf28rr.qdimacs': True,
        '133.rf_reduced.qdimacs': True,
        '134.s713_d4_s.qdimacs': True,
        '135.s1269_d2_s.qdimacs': True,
        '136.s5378_1_0.qdimacs': True,
        '137.s05378_PR_7_2.qdimacs.txt': True,
        '138.s15850_PR_5_90.qdimacs': False,
        '139.s38584_PR_1_2.qdimacs': True,
        '14.a2r.qdimacs': False,
        '140.segfault.qdimacs': True,
        '141.segfault2.qdimacs': True,
        '142.simple_sat.qdimacs': True,
        '143.simple_seperated.qdimacs': True,
        '144.sns53_reduced.qdimacs': True,
        '145.sns56rrr.qdimacs': True,
        '146.sorting_network_4_5_reduced.qdimacs': True,
        '147.sorting_network_4_5_rr.qdimacs': False,
        '148.sortnetsort5AEstepl003_reduced.qdimacs': False,
        '149.stmt5rr.qdimacs': True,
        '150.stmt7rr.qdimacs': True,
        '151.stmt21_4_5_reduced.qdimacs': False,
        '152.stmt21r4.qdimacs': True,
        '153.stmt21rr.qdimacs': True,
        '154.stmt27_149_224.qdimacs.txt': False,
        '156.test_implications.qdimacs': False,
        '157.test_sat.qdimacs': True,
        '158.test_unsat.qdimacs': False,
        '159.tmp-47850_reduced.qdimacs': True,
        '16.arbiter_bug2.qdimacs': False,
        '16.arbiter_bug2.qdimacs~': False,
        '17.arbiter_reduced.qdimacs': True,
        '18.asdf2.qdimacs': False,
        '19.asdf4_reduced.qdimacs': True,
        '2.SAT.dimacs': True,
        '20.asdf_reduced.qdimacs': True,
        '21.b17-4.qdimacs': False,
        '22.b17-4r.qdimacs': False,
        '23.biu.qdimacs': True,
        '24.biubug.qdimacs': True,
        '25.biu_manual.qdimacs': True,
        '26.blocks_reduced.qdimacs': True,
        '27.br.qdimacs': True,
        '28.br3_reduced.qdimacs': False,
        '29.brrr.qdimacs': True,
        '3.UNSAT.dimacs': False,
        '30.bug1.qdimacs': False,
        '31.bug3.qdimacs': False,
        '32.bug5.qdimacs': True,
        '33.bug6.qdimacs': True,
        '34.bug6_reduced.qdimacs': False,
        '35.bug6rr.qdimacs': True,
        '36.bug6rrmod.qdimacs': True,
        '37.bug7.qdimacs': False,
        '38.bug8.qdimacs': False,
        '39.bug9.qdimacs': True,
        '4.UNSAT.dimacs': False,
        '41.bug10rrr.qdimacs': False,
        '42.bug17.qdimacs': False,
        '43.bug_abort.qdimacs': True,
        '44.bug_diverge.qdimacs': True,
        '45.bug_diverge2.qdimacs': True,
        '46.bug_lights.qdimacs': True,
        '47.bug_refinement.qdimacs': False,
        '48.bug_refinement_reduced2.qdimacs': False,
        '5.UNSAT.dimacs': False,
        '51.dungeon_i15-m75-u10-v0.pddl_planlen=4.qdimacs': True,
        '52.c5_BMC_p1_k4.qdimacs': True,
        '54.constants_and_elimination.qdimacs': True,
        '57.dungeon_i25-m125-u3-v0.pddl_planlen=13.bloqqer.qdimacs': True,
        '58.dungeon_i25-m125-u3-v0.pddl_planlen=13.qdimacs': True,
        '59.dungeon_i25-m125-u3-v0.pddl_planlen=14.qdimacs': True,
        '6.SAT.dimacs': True,
        '60.eequery_query04_1344n.qdimacs': True,
        '61.eequery_query04_1344n.qdimacs.txt': True,
        '62.eequery_query04_1344nqdimacs_reduced.txt': False,
        '63.eequery_query04_1344n_reduced.qdimacs': True,
        '64.eer.qdimacs': False,
        '65.eerr.qdimacs': False,
        '66.empty_clause.qdimacs': False,
        '67.equal.qdimacs': True,
        '68.equal_hidden.qdimacs': False,
        '69.equality_hidden.qdimacs': False,
        '7.SAT.qdimacs': True,
        '7.SAT.qdimacs_to_dimacs.cnf': True,
        '70.err.qdimacs': True,
        '71.ev-pr-4x4-5-3-0-0-1-s.qdimacs': True,
        '72.ev-pr-4x4-7-3-0-0-1-s.qdimacs': True,
        '73.example.qdimacs': False,
        '74.false.qdimacs': False,
        '74.false.qdimacs~': False,
        '75.frrr.qdimacs': True,
        '76.fuzz.qdimacs': True,
        '76.fuzz1.qdimacs': False,
        '77.fuzz606.qdimacs': False,
        '78.fuzz1380_reduced.qdimacs': True,
        '79.fuzz7300.qdimacs': False,
        '8.SAT.qdimacs': True,
        '80.fuzz9716.qdimacs': False,
        '81.fuzz10825.qdimacs': False,
        '82.fuzz10825_reduced.qdimacs': False,
        '83.fuzz12668_reduced.qdimacs': True,
        '84.fuzz12891.qdimacs': False,
        '85.fuzz14807_reduced.qdimacs': False,
        '86.fuzz17061.qdimacs': True,
        '87.fuzz19494_reduced.qdimacs': False,
        '88.fuzz19959.qdimacs': True,
        '89.fuzz22644.qdimacs': True,
        '9.SAT.qdimacs': True,
        '90.fuzz23979_reduced.qdimacs': False,
        '91.fuzz24003_reduced.qdimacs': False,
        '92.fuzz24330.qdimacs': True,
        '93.fuzz25823.qdimacs': False,
        '94.illegal_dependence_conflict.qdimacs': False,
        '95.illegal_dependence_conflict2.qdimacs': False,
        '96.incomplete_or.qdimacs': True,
        '97.k_ph_n-16.qdimacs': True,
        '98.lights.qdimacs': False,
        '99.lights3_021_0_009.qdimacs': True,
    }

    for filename in results.keys():
        print(f'--- Processing {filename} ... ')
        file_path = os.path.join(directory, filename)
        nv, nc, clauses, quantifiers = read_qdimacs_from_file_unchecked(file_path)
        print(f"\tVars={nv} - Clauses={nc}")
        
        clean_caches()

        t0 = time()
        res = None
        try:
            with time_limit(timeout):
                res = inf_solver(quantifiers, clauses)
            t1 = time()
            print(f"{'CORRECT' if res == results[filename] else 'INCORRECT'} {'SAT' if res else 'UNSAT'}")
            print(f"Time: {t1 - t0 : .4f} seconds")
        except TimeoutException:
            t1 = time()
            print(f"TIMEOUT after {t1 - t0 : .4f} seconds for {filename}!")
            print("Consider increasing the timeout or optimizing the solver.")
        except Exception as e:
            t1 = time()
            print(f"An unexpected error occurred for {filename}: {e}")
            print(f"Time elapsed before error: {t1 - t0 : .4f} seconds")
        print("-" * 40) # Separador para mejor legibilidad

##############################################################################################
### MAIN #####################################################################################

if __name__ == '__main__':
    test_integration(15)