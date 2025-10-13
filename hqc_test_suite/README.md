# HQC Sampling Method Test Suite

## Overview

This directory contains a test suite for benchmarking and analyzing different vector sampling algorithms within the HQC implementation of the `liboqs` project. It is designed to automate the entire workflow:

1.  Building `liboqs` with a specific sampling method.
2.  Running performance (speed) and memory usage tests.
3.  Generating raw data (`.csv` files) from the benchmarks.
4.  Visualizing the results as chart images (`.png` files).

## Directory Structure

```
hqc_test_suite/
├── run_full_test_suite.sh    # The main executable script to run everything.
├── README.md                 # This file.
├── data/
│   ├── memory/               # Stores raw CSV data from memory benchmarks.
│   └── performance/          # Stores raw CSV data from speed benchmarks.
├── results/
│   ├── memory_charts/        # Stores output PNG charts for memory usage.
│   └── performance_charts/   # Stores output PNG charts for performance.
└── scripts/
    ├── measure_memory.py       # Python script to measure memory usage.
    ├── visualize_memory.py     # Python script to visualize memory data.
    └── visualize_performance.py# Python script to visualize performance data.
```

## How to Run

### Prerequisites

Ensure that the main `liboqs` project has been configured and built at least once, so that the `build/` directory exists.

### Execution

To run the entire test suite, simply execute the main shell script. You can do this from the `liboqs` root directory or from within the `hqc_test_suite` directory.

```bash
# From the liboqs root directory:
./hqc_test_suite/run_full_test_suite.sh
```

The script will then perform all steps automatically. It will print its progress to the console.

## Output

After the script finishes, you will find:

-   **Raw Data:** All benchmark data in `.csv` format inside the `data/` subdirectories.
-   **Result Charts:** All generated plots in `.png` format inside the `results/` subdirectories.

## Customization

The main script `run_full_test_suite.sh` contains a configuration section at the top where you can easily change parameters such as the list of algorithms to test or the number of iterations for the speed test.
