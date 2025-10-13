

import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import os
import sys
import glob

def get_hqc_level():
    """Gets the HQC security level from command-line arguments."""
    if len(sys.argv) < 2 or sys.argv[1] not in ['128', '192', '256']:
        print("Usage: python3 visualize_performance.py <level>")
        print("  <level> must be one of: 128, 192, 256")
        sys.exit(1)
    return sys.argv[1]

# --- Data Loading ---
level = get_hqc_level()
script_dir = os.path.dirname(os.path.realpath(__file__))
print(f"--- Generating visualization for HQC-{level} ---")

# Use glob to find all relevant CSV files based on the level
search_path = os.path.join(script_dir, "..", "data", "performance", f'hqc{level}_*_data.csv')
file_paths = glob.glob(search_path)

if not file_paths:
    print(f"Warning: No data files found matching '{search_path}'. Exiting.")
    sys.exit(0)

print(f"Found data files: {file_paths}")

# Read and combine the data from the files
data_frames = []
for f_path in file_paths:
    try:
        df = pd.read_csv(f_path)
        # Create a 'source' column to identify the data's origin
        source_name = os.path.basename(f_path).replace(f'hqc{level}_', '').replace('_data.csv', '')
        df['source'] = source_name
        data_frames.append(df)
    except FileNotFoundError:
        print(f"Warning: File not found at {f_path}")

if not data_frames:
    print("No data could be loaded. Exiting.")
    exit()

# Combine all data into a single DataFrame
combined_df = pd.concat(data_frames, ignore_index=True)

# --- Visualization ---
print("Generating performance comparison plot with independent y-axis subplots...")

# Set the style for the plot
sns.set_style("whitegrid")

# The operations we want to plot
operations = ['keypair', 'encaps', 'decaps']

# Create a figure with 3 subplots side-by-side, with INDEPENDENT y-axes
fig, axes = plt.subplots(1, len(operations), figsize=(24, 8), sharey=False)
fig.suptitle(f'HQC-{level} Performance Comparison', fontsize=20, fontweight='bold')

# Loop through each operation and its corresponding subplot axis
for i, op in enumerate(operations):
    ax = axes[i]
    
    # Filter data for the current operation
    op_data = combined_df[combined_df['operation'] == op]
    
    # Create the boxplot on the current axis
    sns.boxplot(x='source', y='cycles', hue='source', data=op_data, ax=ax, palette='viridis', legend=False)
    
    # Set subplot titles and labels
    ax.set_title(f'Operation: {op}', fontsize=16, fontweight='bold')
    ax.set_xlabel('Data Source', fontsize=12)
    ax.set_ylabel('CPU Cycles (Log Scale)', fontsize=12)
    
    # Set y-axis to log scale for each subplot individually
    ax.set_yscale('log')
    ax.tick_params(axis='x', labelsize=12)
    ax.tick_params(axis='y', labelsize=10)


# Adjust layout and save the plot
plt.tight_layout(rect=[0, 0.03, 1, 0.95])
output_dir = os.path.join(script_dir, "..", "results", "performance_charts")
os.makedirs(output_dir, exist_ok=True)
output_filename = os.path.join(output_dir, f'hqc{level}_performance.png')
plt.savefig(output_filename, dpi=300, bbox_inches='tight')

print(f"Successfully created the plot and saved it as '{output_filename}'")

# --- Summary Statistics ---
print("\n--- Median CPU Cycles per Operation ---")
# Calculate and display the median cycles for each operation and source
median_cycles = combined_df.groupby(['source', 'operation'])['cycles'].median().unstack()
print(median_cycles.to_string())
print("\nThis table shows the median (50th percentile) CPU cycles for each category.")

# --- Summary Statistics ---
print("\n--- Summary Statistics for CPU Cycles per Operation ---")
# Calculate and display summary statistics (mean, median, quartiles, etc.)
summary_stats = combined_df.groupby(['source', 'operation'])['cycles'].describe()
print(summary_stats.to_string())
print("\nThis table shows key statistics for each category:")
print("- mean: Average CPU cycles")
print("- 50%: Median (the 50th percentile)")
print("- 25%: First Quartile (Q1)")
print("- 75%: Third Quartile (Q3)")
