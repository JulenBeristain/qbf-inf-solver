import subprocess
import os
import psutil
import time
import csv
import copy
import sys
import statistics
from pdb import set_trace

from qbf_parser import read_qdimacs_from_file_unchecked
from types_qbf import *

def get_instance_info(instance_path: str) -> Dict:
    """
    * número de variables, número de cláusulas, 
    * tamaños de cláusulas media, minima, maxima, mediana, standard deviation, 
    * número de bloques de cuantificadores
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

    return {
        'Variables': nv,
        'Clauses': nc,
        'Clause_SZ_Mean': mean,
        'Clause_SZ_Min': min_,
        'Clause_SZ_Max': max_,
        'Clause_SZ_Median': median,
        'Clause_SZ_StdDev': std_dev,
        'QBlocks': nb,
    }


def run_solver(solver_path, instance_path, timeout_seconds):
    """
    Runs a QBF solver on an instance and collects metrics.
    Returns a dictionary with results.
    """
    command = [solver_path, instance_path]
    
    start_time_wall = time.time()
    process = None
    peak_memory_mb = 0
    cpu_time_user = 0
    cpu_time_system = 0
    exit_status = "UNKNOWN"
    solver_output = "TIMEOUT" # To store stdout/stderr for debugging if needed

    try:
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True  # Decode stdout/stderr as text
        )
        
        while process.poll() is None and (time.time() - start_time_wall) < timeout_seconds:
            try:
                p = psutil.Process(process.pid)
                # Check current memory usage of the process and its children
                mem_info = p.memory_info()
                current_rss_mb = mem_info.rss / (1024 * 1024)
                peak_memory_mb = max(peak_memory_mb, current_rss_mb)

                # Get CPU times - cumulative for the process and its children
                cpu_times = p.cpu_times()
                cpu_time_user = cpu_times.user + cpu_times.children_user
                cpu_time_system = cpu_times.system + cpu_times.children_system
                
                time.sleep(0.1) # Poll every 100ms
            except psutil.NoSuchProcess:
                # Process might have just finished
                break
        
        # If the process is still running after the loop (due to timeout)
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5) # Give it a little time to terminate
            except subprocess.TimeoutExpired:
                process.kill() # Force kill if it doesn't terminate
            exit_status = "TIMEOUT"
            cpu_time_user = timeout_seconds * 2 # Penalty for timeout
            cpu_time_system = timeout_seconds * 2 # Penalty for timeout
        else:
            stdout, stderr = process.communicate()
            solver_output = stdout.strip() # + stderr
            assert solver_output == 'SAT' or solver_output == 'UNSAT', f"La salida del solver no es SAT o UNSAT, sino: -{solver_output}-"
            
            # TODO: determinar si el resultado es correcto o incorrecto en base a los primeros resultados que obtengamos con DepQBF
            #if process.returncode == 0:
            #    exit_status = "SOLVED"
            #else:
            #    exit_status = f"ERROR ({process.returncode})"
            exit_status = 'CORRECT' # Con DepQBF
            
            # Get final CPU and memory usage after process finishes
            try:
                p = psutil.Process(process.pid)
                mem_info = p.memory_info()
                current_rss_mb = mem_info.rss / (1024 * 1024)
                peak_memory_mb = max(peak_memory_mb, current_rss_mb) # One last check
                
                cpu_times = p.cpu_times()
                cpu_time_user = cpu_times.user + cpu_times.children_user
                cpu_time_system = cpu_times.system + cpu_times.children_system

            except psutil.NoSuchProcess:
                # Process might be gone if it finished just before final check
                pass

    # TODO: asegurarme de que no haya estas excepciones con ninguna instancia
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

    total_cpu_time = cpu_time_user + cpu_time_system
    
    execution_info = {
        "instance": os.path.basename(instance_path),
        "solver_output": solver_output,
        "status": exit_status,
        #"cpu_time_user": round(cpu_time_user, 3),
        #"cpu_time_system": round(cpu_time_system, 3),
        "total_cpu_time": round(total_cpu_time, 3),
        "peak_memory_mb": round(peak_memory_mb, 2),
    }
    return execution_info

if __name__ == "__main__":
    
    # Indicar aquí el solver
    solver_name, solver_path = "DepQBF", "depqbf"
    
    instance_dir = "/home/julen/integration_tests"
    instances = [os.path.join(instance_dir, f) for f in os.listdir(instance_dir)]
    
    timeout = 900 # seconds (15 minutes)
    num_executions_per_instace = 10 # para estabilizar resultados

    all_results = []
    instance_results = []

    print(f"Benchmarking {solver_name}...")
    for instance_path in sorted(instances): # Sort for consistent order
        print(f"  Running {solver_name} on {os.path.basename(instance_path)}...")

        for _ in range(num_executions_per_instace):
            result = run_solver(solver_path, instance_path, timeout)
            result["solver_name"] = solver_name
            instance_results.append(result)
            if result['status'] == 'TIMEOUT':
                print("TIMEOUT! Filling the rest of the tries with this result ...")
                remaining_tries = num_executions_per_instace - len(instance_results)
                instance_results.extend( result for _ in range(remaining_tries) )

            #print(f"    Status: {result['status']}, CPU Time: {result['total_cpu_time']}s, Peak Mem: {result['peak_memory_mb']}MB")
        
        aggregate = copy.deepcopy(result)
        aggregate['total_cpu_time'] = sum(r['total_cpu_time'] for r in instance_results) / len(instance_results)
        aggregate['peak_memory_mb'] = sum(r['peak_memory_mb'] for r in instance_results) / len(instance_results)
        instance_info = get_instance_info(instance_path)
        all_results.append(aggregate | instance_info)
        
        print(f"    Status: {aggregate['status']}, CPU Time: {aggregate['total_cpu_time']}s, Peak Mem: {aggregate['peak_memory_mb']}MB")

    # Save results to a CSV file
    output_csv_file = f"{solver_name}_benchmark_results.csv"
    if all_results:
        keys = all_results[0].keys()
        with open(output_csv_file, 'w', newline='') as output_file:
            dict_writer = csv.DictWriter(output_file, fieldnames=keys)
            dict_writer.writeheader()
            dict_writer.writerows(all_results)
        print(f"\nBenchmark results saved to {output_csv_file}")

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

    time_correct = [res['total_cpu_time'] for res in all_results if res['status'] == 'CORRECT']
    if time_correct:
        time_correct_mean = statistics.mean(time_correct)
        time_correct_min = min(time_correct)
        time_correct_max = max(time_correct)
        time_correct_median = statistics.median(time_correct)
        time_correct_std_dev = statistics.stdev(time_correct) if len(time_correct) > 1 else 0.0
    else:
        time_correct_mean = time_correct_min = time_correct_max = time_correct_median = time_correct_std_dev = 'None'

    time_penalized = [res['total_cpu_time'] for res in all_results if res['status'] != 'INCORRECT']
    if time_penalized:
        time_penalized_mean = statistics.mean(time_penalized)
        time_penalized_min = min(time_penalized)
        time_penalized_max = max(time_penalized)
        time_penalized_median = statistics.median(time_penalized)
        time_penalized_std_dev = statistics.stdev(time_penalized) if len(time_penalized) > 1 else 0.0
    else:
        time_penalized_mean = time_penalized_min = time_penalized_max = time_penalized_median = time_penalized_std_dev = 'None'

    memory_usage = [res['peak_memory_mb'] for res in all_results if res['status'] != 'INCORRECT']
    if memory_usage:
        memory_mean = statistics.mean(memory_usage)
        memory_min = min(memory_usage)
        memory_max = max(memory_usage)
        memory_median = statistics.median(memory_usage)
        memory_std_dev = statistics.stdev(memory_usage) if len(memory_usage) > 1 else 0.0
    else:
        memory_mean = memory_min = memory_max = memory_median = memory_std_dev = 'None'

    aggregate_data = {
        'solver_name': solver_name,
        'instance_num': num_instances,
        'correct_num': num_correct,
        'correct_per': per_correct,
        'incorrect_num': num_incorrect,
        'per_incorrect': per_incorrect,
        'timeout_num': num_timeout,
        'timeout_per': per_timeout,
        'time_correct_s_mean': time_correct_mean,
        'time_correct_s_min': time_correct_min,
        'time_correct_s_max': time_correct_max,
        'time_correct_s_median': time_correct_median,
        'time_correct_s_std_dev': time_correct_std_dev,
        'time_penalized_s_mean': time_penalized_mean,
        'time_penalized_s_min': time_penalized_min,
        'time_penalized_s_max': time_penalized_max,
        'time_penalized_s_median': time_penalized_median,
        'time_penalized_s_std_dev': time_penalized_std_dev,
        'memory_peak_mb_mean': memory_mean,
        'memory_peak_mb_min': memory_min,
        'memory_peak_mb_max': memory_max,
        'memory_peak_mb_median': memory_median,
        'memory_peak_mb_std_dev': memory_std_dev,
    }

    aggregate_csv_file = f"{solver_name}_benchmark_aggregate.csv"
    keys = aggregate_data.keys()
    with open(aggregate_csv_file, 'w', newline='') as output_file:
        dict_writer = csv.DictWriter(output_file, fieldnames=keys)
        dict_writer.writeheader()
        dict_writer.writerows(aggregate_data)
    print(f"\nBenchmark aggregate results saved to {aggregate_csv_file}")
