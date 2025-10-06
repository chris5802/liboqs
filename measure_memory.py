
import subprocess
import re
import sys
import os
import csv

# --- Configuration ---
# You can change the algorithms to test and the number of runs here
ALGORITHMS_TO_TEST = ["HQC-128", "HQC-192", "HQC-256"]
RUNS_PER_OPERATION = 1000
OUTPUT_CSV_FILE = "memory_latest_benchmark_raw_data.csv"
# --- End Configuration ---


def run_single_measurement(command):
    """Runs the command once and returns the memory usage in bytes, or None on failure."""
    try:
        # The output of /usr/bin/time -l goes to stderr
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=True,
            timeout=30  # Add a timeout to prevent hangs
        )
        output = result.stderr
    except subprocess.CalledProcessError as e:
        output = e.stderr
        if "maximum resident set size" not in output:
            print(f"\nError during subprocess execution: {e.stderr}")
            return None
    except subprocess.TimeoutExpired:
        print("\nError: A test run timed out.")
        return None

    match = re.search(r'(\d+)\s+maximum resident set size', output)
    if match:
        return int(match.group(1))
    
    print(f"\nWarning: Could not parse memory usage from output.\nOutput was:\n{output}")
    return None


def main():
    """
    Measures memory usage for a list of KEM algorithms, runs N times,
    and outputs every single run's result to a CSV file for later analysis.
    """
    executable = "./build/tests/test_kem_mem"
    if not os.path.exists(executable):
        print(f"Error: Executable not found at {executable}")
        print("Please ensure the project has been built.")
        return

    operations = {"keygen": "0", "encaps": "1", "decaps": "2"}

    print("--- Starting Raw Data Memory Benchmark ---")
    print(f"Algorithms to test: {', '.join(ALGORITHMS_TO_TEST)}")
    print(f"Runs per operation: {RUNS_PER_OPERATION}")
    print(f"Output CSV file: {OUTPUT_CSV_FILE}")
    print("-" * 30)

    try:
        with open(OUTPUT_CSV_FILE, 'w', newline='') as csvfile:
            csv_writer = csv.writer(csvfile)
            # Write the header row
            header = ["algorithm", "operation", "run_number", "memory_bytes"]
            csv_writer.writerow(header)

            for alg_name in ALGORITHMS_TO_TEST:
                print(f"\nProcessing algorithm: {alg_name}")
                for op_name, op_num in operations.items():
                    print(f"  -> Operation: {op_name}...")
                    
                    command = ["/usr/bin/time", "-l", executable, alg_name, op_num]
                    
                    for i in range(RUNS_PER_OPERATION):
                        progress = i + 1
                        print(f"\r     Run {progress}/{RUNS_PER_OPERATION}", end="")
                        
                        mem_bytes = run_single_measurement(command)
                        
                        if mem_bytes is not None:
                            # Write data for each individual run immediately to the CSV
                            csv_writer.writerow([alg_name, op_name, progress, mem_bytes])
                    
                    print() # Move to the next line after the progress indicator is done
                    print("     Done.")

    except IOError as e:
        print(f"\nError writing to CSV file: {e}")
        return

    print(f"\nBenchmark complete. All raw data has been saved to {OUTPUT_CSV_FILE}.")


if __name__ == "__main__":
    main()
