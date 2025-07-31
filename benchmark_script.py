import subprocess
import os
import psutil
import time
import csv

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
    solver_output = "" # To store stdout/stderr for debugging if needed

    try:
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True  # Decode stdout/stderr as text
        )

        # Monitor CPU time and memory usage periodically
        # You'll need to adapt this for your specific OS and psutil usage
        # This is a simplified example; a robust solution might poll more frequently
        # or use a separate monitoring thread.
        # For peak memory, you need to track `rss` over time.
        
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
            peak_memory_mb = 0 # Or max_memory_limit if you want to record that it hit the limit
        else:
            stdout, stderr = process.communicate()
            solver_output = stdout + stderr
            if process.returncode == 0:
                exit_status = "SOLVED"
            else:
                exit_status = f"ERROR ({process.returncode})"
            
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


    except FileNotFoundError:
        exit_status = "SOLVER_NOT_FOUND"
    except Exception as e:
        exit_status = f"SCRIPT_ERROR: {e}"

    total_cpu_time = cpu_time_user + cpu_time_system
    
    return {
        "instance": os.path.basename(instance_path),
        "solver": os.path.basename(solver_path),
        "status": exit_status,
        "cpu_time_user": round(cpu_time_user, 3),
        "cpu_time_system": round(cpu_time_system, 3),
        "total_cpu_time": round(total_cpu_time, 3),
        "peak_memory_mb": round(peak_memory_mb, 2),
        "solver_output": solver_output.strip() # Store for debugging
    }

# --- Main Benchmarking Logic ---
if __name__ == "__main__":
    solvers = {
        "solverA": "./path/to/solverA_executable",
        "solverB": "./path/to/solverB_executable",
        # Add more solvers
    }
    
    # Assuming instances are in a directory named "benchmarks"
    instance_dir = "benchmarks"
    instances = [os.path.join(instance_dir, f) for f in os.listdir(instance_dir) if f.endswith(".qbf")]
    
    timeout = 900 # seconds (15 minutes)
    
    all_results = []

    for solver_name, solver_path in solvers.items():
        print(f"Benchmarking {solver_name}...")
        for instance_path in sorted(instances): # Sort for consistent order
            print(f"  Running {solver_name} on {os.path.basename(instance_path)}...")
            result = run_solver(solver_path, instance_path, timeout)
            result["solver_name"] = solver_name # Add descriptive solver name
            all_results.append(result)
            print(f"    Status: {result['status']}, CPU Time: {result['total_cpu_time']}s, Peak Mem: {result['peak_memory_mb']}MB")

    # Save results to a CSV file
    output_csv_file = "qbf_benchmark_results.csv"
    if all_results:
        keys = all_results[0].keys()
        with open(output_csv_file, 'w', newline='') as output_file:
            dict_writer = csv.DictWriter(output_file, fieldnames=keys)
            dict_writer.writeheader()
            dict_writer.writerows(all_results)
        print(f"\nBenchmark results saved to {output_csv_file}")