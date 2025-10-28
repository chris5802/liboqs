#!/bin/bash
#
# This script automates the entire process of testing HQC sampling methods.
# It can be run from any directory.

# Exit immediately if any command fails
set -e

# --- Configuration ---
# Find the script's own directory, to make all paths relative to it
SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)

TEST_SUITE_DIR="${SCRIPT_DIR}"
LIBOQS_DIR="${TEST_SUITE_DIR}/.."
BUILD_DIR="${LIBOQS_DIR}/build"

SPEED_KEM_EXEC="${BUILD_DIR}/tests/speed_kem"
MEASURE_MEM_SCRIPT="${TEST_SUITE_DIR}/scripts/measure_memory.py"
VISUALIZE_PERF_SCRIPT="${TEST_SUITE_DIR}/scripts/visualize_performance.py"
VISUALIZE_MEM_SCRIPT="${TEST_SUITE_DIR}/scripts/visualize_memory.py"

# Define the methods and levels to test
METHODS=(1 2 3 4)
METHOD_NAMES=("original" "latest" "ctus" "fixed-n")
LEVELS=(128 192 256)
SPEED_TEST_ITERATIONS=10000

# --- Activate Python Virtual Environment ---
VENV_ACTIVATE="${LIBOQS_DIR}/.venv/bin/activate"
if [ -f "${VENV_ACTIVATE}" ]; then
    echo "Activating Python virtual environment..."
    source "${VENV_ACTIVATE}"
else
    echo "Warning: Python virtual environment not found at ${VENV_ACTIVATE}"
    echo "The script will use the system's default python3. This may fail if packages are not installed globally."
fi

# --- Verification ---
if [ ! -d "${BUILD_DIR}" ]; then
    echo "Error: Build directory not found at ${BUILD_DIR}"
    echo "Please run the initial cmake and ninja build first."
    exit 1
fi

if [ ! -f "${SPEED_KEM_EXEC}" ]; then
    echo "Error: speed_kem executable not found at ${SPEED_KEM_EXEC}"
    exit 1
fi

# --- Main Test Loop ---
echo "========================================="
echo "===   Starting Full HQC Test Suite    ==="
echo "========================================="

for i in "${!METHODS[@]}"; do
    METHOD=${METHODS[$i]}
    METHOD_NAME=${METHOD_NAMES[$i]}

    echo ""
    echo "-------------------------------------------------"
    echo "--- Testing Method ${METHOD}: ${METHOD_NAME}"
    echo "-------------------------------------------------"

    # 1. Configure for the current method
    echo "[Step 1/4] Configuring for ${METHOD_NAME}..."
    # Run cmake from within the test suite directory, pointing to the build dir
    cmake -DHQC_SAMPLING_METHOD=${METHOD} "${BUILD_DIR}"

    # 2. Build the library with the new configuration
    echo "[Step 2/4] Building library with ninja..."
    ninja -C "${BUILD_DIR}"

    # 3. Run Performance Tests for all levels
    echo "[Step 3/4] Running performance tests..."
    for LEVEL in "${LEVELS[@]}"; do
        ALG_NAME="HQC-${LEVEL}"
        OUTPUT_CSV="${TEST_SUITE_DIR}/data/performance/hqc${LEVEL}_${METHOD_NAME}_data.csv"
        echo "  -> Testing ${ALG_NAME}, outputting to ${OUTPUT_CSV}"
        "${SPEED_KEM_EXEC}" -n ${SPEED_TEST_ITERATIONS} -o "${OUTPUT_CSV}" "${ALG_NAME}"
    done

    # 4. Run Memory Test
    echo "[Step 4/4] Running memory test..."
    MEM_OUTPUT_CSV="${TEST_SUITE_DIR}/data/memory/memory_${METHOD_NAME}_benchmark_raw_data.csv"
    echo "  -> Outputting to ${MEM_OUTPUT_CSV}"
    python3 "${MEASURE_MEM_SCRIPT}" "${MEM_OUTPUT_CSV}"

done

# --- Final Visualization ---
# Change to the test suite directory so python scripts can find their data
cd "${TEST_SUITE_DIR}"

echo ""
echo "-------------------------------------------------"
echo "---         Generating Visualizations         ---"
echo "-------------------------------------------------"

# 1. Visualize Memory Results
echo "[Step 1/2] Visualizing memory results..."
python3 "${VISUALIZE_MEM_SCRIPT}"

# 2. Visualize Performance Results
echo "[Step 2/2] Visualizing performance results..."
for LEVEL in "${LEVELS[@]}"; do
    echo "  -> Generating graph for HQC-${LEVEL}"
    python3 "${VISUALIZE_PERF_SCRIPT}" "${LEVEL}"
done

echo ""
echo "========================================="
echo "===      Test Suite Finished          ==="
echo "========================================="
echo "All tests completed and visualizations generated."