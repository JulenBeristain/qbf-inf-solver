import subprocess
import os
#import psutil
import time
import csv
import copy
import sys
import statistics
from pdb import set_trace

from qbf_parser import read_qdimacs_from_file_unchecked
from types_qbf import *

RESULTS = {
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
    '15.adder2.qdimacs': 'TIMEOUT',
    '150.stmt7rr.qdimacs': True,
    '151.stmt21_4_5_reduced.qdimacs': False,
    '152.stmt21r4.qdimacs': True,
    '153.stmt21rr.qdimacs': True,
    '154.stmt27_149_224.qdimacs.txt': False,
    '155.stmt27rrr.qdimacs': False,
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
    '40.bug10rr.qdimacs': 'TIMEOUT',
    '41.bug10rrr.qdimacs': False,
    '42.bug17.qdimacs': False,
    '43.bug_abort.qdimacs': True,
    '44.bug_diverge.qdimacs': True,
    '45.bug_diverge2.qdimacs': True,
    '46.bug_lights.qdimacs': True,
    '47.bug_refinement.qdimacs': False,
    '48.bug_refinement_reduced2.qdimacs': False,
    '49.c1_BMC_p1_k8.qdimacs': 'TIMEOUT',
    '5.UNSAT.dimacs': False,
    '50.c3_BMC_p1_k256.qdimacs': 'TIMEOUT',
    '51.dungeon_i15-m75-u10-v0.pddl_planlen=4.qdimacs': True,
    '52.c5_BMC_p1_k4.qdimacs': True,
    '53.C499.blif_0.10_0.20_0_0_inp_exact.qdimacs': 'TIMEOUT',
    '54.constants_and_elimination.qdimacs': True,
    '55.driverlog09_8.qdimacs': 'TIMEOUT',
    '56.driverlog10_7.qdimacs': 'TIMEOUT',
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

def run_solver(solver_path, instance_path, timeout_seconds, python=False):
    """
    Runs a QBF solver on an instance and collects the spent wall time.
    """
    command = [solver_path, instance_path]
    if python:
        command = ['python3'] + command

    exit_status = "UNKNOWN"
    solver_output = "TIMEOUT" # To store stdout/stderr for debugging if needed
    start_time_wall = time.time()

    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=timeout_seconds, check=False)
        total_time_wall = time.time() - start_time_wall
        
        solver_output = result.stdout.strip() #+ result.stderr.strip()
        assert solver_output == 'SAT' or solver_output == 'UNSAT', f"La salida del solver no es SAT o UNSAT, sino: -{solver_output}-"
    
        instance = os.path.basename(instance_path)
        if solver_output == 'SAT' and RESULTS[instance] is True:
            exit_status = 'CORRECT'
        elif solver_output == 'UNSAT' and RESULTS[instance] is False:
            exit_status = 'CORRECT'
        elif RESULTS[instance] == 'TIMEOUT':
            exit_status = "EUREKA!"
        else:
            exit_status = 'INCORRECT'

    except subprocess.TimeoutExpired as e:
        exit_status = "TIMEOUT"
        total_time_wall = 2 * timeout_seconds # Penalty for timeout
        
    except subprocess.CalledProcessError as e:
        print(f"Subprocess failed with error: {e}", file=sys.stderr)
        sys.stderr.flush()
        sys.exit(3)
    except FileNotFoundError:
        exit_status = "SOLVER_NOT_FOUND"
        print(exit_status, file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    except Exception as e:
        exit_status = f"SCRIPT_ERROR: {e}"
        print(exit_status, file=sys.stderr)
        sys.stderr.flush()
        set_trace()
        sys.exit(2)
    
    execution_info = {
        "instance": os.path.basename(instance_path),
        "solver_output": solver_output,
        "status": exit_status,
        "total_wall_time": round(total_time_wall, 3),
    }
    return execution_info

if __name__ == "__main__":
    
    # Indicar aquí el solver
    solver_name, solver_path, python = "DepQBF", "depqbf", False
    #solver_name, solver_path, python = "Naive", "/home/julen/TFG/qbf_naive_solver.py", True
    #solver_name, solver_path, python = "NaivePre", "/home/julen/TFG/qbf_naive_solver_pre.py", True
    #solver_name, solver_path, python = "FNI", "home/julen/TFG/qbf_inf_final.py", True
    
    iterative_experimentation = True
    
    instance_dir = "/home/julen/integration_tests"
    if iterative_experimentation:
        instances = [os.path.join(instance_dir, f) for f in INSTANCES_ITER_EXP]
    else:
        instances = [os.path.join(instance_dir, f) for f in os.listdir(instance_dir)]
    
    timeout_s = (1 if iterative_experimentation else 15) * 60
    num_executions_per_instace = 3 if iterative_experimentation else 10 # para estabilizar resultados

    all_results = []

    print(f"Benchmarking {solver_name}...")
    for instance_path in sorted(instances): # Sort for consistent order
        print(f"  Running {solver_name} on {os.path.basename(instance_path)}...")

        instance_results = []
        for _ in range(num_executions_per_instace):
            result = run_solver(solver_path, instance_path, timeout_s, python=python)
            result["solver_name"] = solver_name
            instance_results.append(result)
            if result['status'] == 'TIMEOUT':
                print("TIMEOUT! Filling the rest of the tries with this result ...")
                remaining_tries = num_executions_per_instace - len(instance_results)
                instance_results.extend( result for _ in range(remaining_tries) )
                break
                
        aggregate = copy.deepcopy(result)
        aggregate['total_wall_time'] = sum(r['total_wall_time'] for r in instance_results) / len(instance_results)
        all_results.append(aggregate)
        
        print(f"    Status: {aggregate['status']}, Wall Time: {aggregate['total_wall_time']}")

    # Save results to a CSV file
    output_csv_file = f"{solver_name}_walltime_results.csv"
    if all_results:
        keys = all_results[0].keys()
        with open(output_csv_file, 'w', newline='') as output_file:
            dict_writer = csv.DictWriter(output_file, fieldnames=keys)
            dict_writer.writeheader()
            dict_writer.writerows(all_results)
        print(f"Walltime results saved to {output_csv_file}")

    # Agregado único por cada solver de todos los datos
    num_instances = len(instances)
    num_correct = num_incorrect = num_timeout = 0
    for res in all_results:
        if res['status'] == 'CORRECT': num_correct += 1
        elif res['status'] == 'INCORRECT': num_incorrect += 1
        elif res['status'] == 'TIMEOUT': num_timeout += 1
        else:
            print(f"Instance {res['instance']} with strange exit status: {res['status']}")
            sys.exit(3)
    per_correct, per_incorrect, per_timeout = (num / num_instances for num in (num_correct, num_incorrect, num_timeout))

    wall_time_correct = [res['total_wall_time'] for res in all_results if res['status'] == 'CORRECT']
    if wall_time_correct:
        wall_time_correct_mean = statistics.mean(wall_time_correct)
        wall_time_correct_min = min(wall_time_correct)
        wall_time_correct_max = max(wall_time_correct)
        wall_time_correct_median = statistics.median(wall_time_correct)
        wall_time_correct_std_dev = statistics.stdev(wall_time_correct) if len(wall_time_correct) > 1 else 0.0
    else:
        wall_time_correct_mean = wall_time_correct_min = wall_time_correct_max = wall_time_correct_median = wall_time_correct_std_dev = 'None'

    wall_time_penalized = [res['total_wall_time'] for res in all_results if res['status'] != 'INCORRECT']
    if wall_time_penalized:
        wall_time_penalized_mean = statistics.mean(wall_time_penalized)
        wall_time_penalized_min = min(wall_time_penalized)
        wall_time_penalized_max = max(wall_time_penalized)
        wall_time_penalized_median = statistics.median(wall_time_penalized)
        wall_time_penalized_std_dev = statistics.stdev(wall_time_penalized) if len(wall_time_penalized) > 1 else 0.0
    else:
        wall_time_penalized_mean = wall_time_penalized_min = wall_time_penalized_max = wall_time_penalized_median = wall_time_penalized_std_dev = 'None'

    aggregate_data = {
        'solver_name': solver_name,
        'instance_num': num_instances,
        'correct_num': num_correct,
        'correct_per': per_correct,
        'incorrect_num': num_incorrect,
        'per_incorrect': per_incorrect,
        'timeout_num': num_timeout,
        'timeout_per': per_timeout,
        
        'wall_time_correct_s_mean':      wall_time_correct_mean,
        'wall_time_correct_s_min':       wall_time_correct_min,
        'wall_time_correct_s_max':       wall_time_correct_max,
        'wall_time_correct_s_median':    wall_time_correct_median,
        'wall_time_correct_s_std_dev':   wall_time_correct_std_dev,
        'wall_time_penalized_s_mean':    wall_time_penalized_mean,
        'wall_time_penalized_s_min':     wall_time_penalized_min,
        'wall_time_penalized_s_max':     wall_time_penalized_max,
        'wall_time_penalized_s_median':  wall_time_penalized_median,
        'wall_time_penalized_s_std_dev': wall_time_penalized_std_dev,
    }

    aggregate_csv_file = f"{solver_name}_walltime_aggregate.csv"
    keys = aggregate_data.keys()
    with open(aggregate_csv_file, 'w', newline='') as output_file:
        dict_writer = csv.DictWriter(output_file, fieldnames=keys)
        dict_writer.writeheader()
        dict_writer.writerow(aggregate_data)
    print(f"Walltime aggregate results saved to {aggregate_csv_file}")
