

import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import os

# --- Data Loading ---
# List of your CSV files
file_paths = [
    '/Users/trista/Documents/Project/oqs_project/liboqs/hqc256_ctus_data.csv',
    '/Users/trista/Documents/Project/oqs_project/liboqs/hqc256_fixed_n_data.csv',
    '/Users/trista/Documents/Project/oqs_project/liboqs/hqc256_latest_data.csv',
    '/Users/trista/Documents/Project/oqs_project/liboqs/hqc256_original_data.csv',
]

# Read and combine the data from the files
data_frames = []
for f_path in file_paths:
    try:
        df = pd.read_csv(f_path)
        # Create a 'source' column to identify the data's origin
        source_name = os.path.basename(f_path).replace('hqc256_', '').replace('_data.csv', '')
        df['source'] = source_name
        data_frames.append(df)
    except FileNotFoundError:
        print(f"Warning: File not found at {f_path}")

if not data_frames:
    print("No data files found. Exiting.")
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
fig.suptitle('HQC-256 Performance Comparison', fontsize=20, fontweight='bold')

# Loop through each operation and its corresponding subplot axis
for i, op in enumerate(operations):
    ax = axes[i]
    
    # Filter data for the current operation
    op_data = combined_df[combined_df['operation'] == op]
    
    # Create the boxplot on the current axis
    sns.boxplot(x='source', y='cycles', data=op_data, ax=ax, palette='viridis')
    
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
output_filename = 'hqc256_performance.png'
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
