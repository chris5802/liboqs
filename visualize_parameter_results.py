'''
This script reads the comprehensive sampling results CSV and generates 
performance and failure rate comparison plots.
'''
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import os
import numpy as np

def plot_final_comparison(df, output_dir):
    '''Generates the final comparison plots as requested by the user.'''
    plt.style.use('seaborn-v0_8-whitegrid')

    # --- Process data ---
    fixed_n_df = df[df['Algorithm'] == 'Fixed-N'].copy()
    fixed_n_df['factor'] = fixed_n_df['Parameter 1'].str.replace('n_iter_', '').astype(float)
    fixed_n_df['Failure Rate (%)'] = 100.0 - fixed_n_df['Success Rate (%)']

    ctus_df = df[df['Algorithm'] == 'CTUS'].copy()
    ctus_df['k_factor'] = ctus_df['Parameter 1'].str.replace('k_', '').astype(float)
    ctus_df['att_factor'] = ctus_df['Parameter 2'].str.replace('att_', '').astype(float)
    diag_df = ctus_df[ctus_df['k_factor'] == ctus_df['att_factor']].copy()
    diag_df['factor'] = diag_df['k_factor']
    diag_df['Failure Rate (%)'] = 100.0 - diag_df['Success Rate (%)']

    # --- Combined Subplots for Failure Rate ---
    # Set figsize to (16, 18) to make each subplot a 16:9 aspect ratio
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(16, 10), sharex=True)
    fig.suptitle('Failure Rate Comparison', fontsize=20, fontweight='bold')

    # Top plot: Fixed-N
    for weight in sorted(fixed_n_df['Weight'].unique()):
        subset = fixed_n_df[fixed_n_df['Weight'] == weight]
        ax1.plot(subset['factor'], subset['Failure Rate (%)'], marker='o', linestyle='-', label=f'Weight = {weight}')
    ax1.set_title('Fixed-N', fontsize=16)
    ax1.set_ylabel('Failure Rate (%)', fontsize=12)
    ax1.legend(title='Weight')
    ax1.grid(True, which='both', linestyle='--', linewidth=0.5)

    # Bottom plot: CTUS
    for weight in sorted(diag_df['Weight'].unique()):
        subset = diag_df[diag_df['Weight'] == weight]
        ax2.plot(subset['factor'], subset['Failure Rate (%)'], marker='x', linestyle='--', label=f'Weight = {weight}')
    ax2.set_title('CTUS', fontsize=16)
    ax2.set_xlabel('Factor', fontsize=12)
    ax2.set_ylabel('Failure Rate (%)', fontsize=12)
    ax2.legend(title='Weight')
    ax2.grid(True, which='both', linestyle='--', linewidth=0.5)

    plt.tight_layout(rect=[0, 0, 1, 0.97]) # Adjust layout for main title
    output_path_subplots = os.path.join(output_dir, "failure_rate_subplots_comparison.png")
    plt.savefig(output_path_subplots, dpi=300)
    plt.close(fig)
    print(f"Saved subplot comparison plot to {output_path_subplots}")

def main():
    '''Main function to run the visualization.'''
    csv_file = 'sampling_results_hyperfine.csv'
    output_dir = 'test_visualizations'

    if not os.path.exists(csv_file):
        print(f"Error: CSV file '{csv_file}' not found.")
        return

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    try:
        df = pd.read_csv(csv_file)
    except Exception as e:
        print(f"Error reading CSV file: {e}")
        return

    plot_final_comparison(df, output_dir)

    print("\nVisualization script finished.")

if __name__ == "__main__":
    main()