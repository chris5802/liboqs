'''
This script reads the comprehensive sampling results CSV and generates 
performance and failure rate comparison plots.
'''
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import os
import numpy as np

def plot_fixed_n_comparison(df, output_dir):
    '''Generates and saves comparison plots for the Fixed-N algorithm.'''
    fixed_n_df = df[df['Algorithm'] == 'Fixed-N'].copy()
    if fixed_n_df.empty:
        print("No data found for Fixed-N algorithm.")
        return

    fixed_n_df['n_iter_factor'] = fixed_n_df['Parameter 1'].str.replace('n_iter_', '').astype(float)
    fixed_n_df['Failure Rate (%)'] = 100.0 - fixed_n_df['Success Rate (%)']

    plt.style.use('seaborn-v0_8-whitegrid')

    # Plot 1: Performance Comparison
    fig1, ax1 = plt.subplots(figsize=(12, 8))
    for weight in sorted(fixed_n_df['Weight'].unique()):
        subset = fixed_n_df[fixed_n_df['Weight'] == weight]
        ax1.plot(subset['n_iter_factor'], subset['Avg. Time (ms)'], marker='o', linestyle='-', label=f'Weight = {weight}')
    ax1.set_title('Fixed-N Performance Comparison', fontsize=16, fontweight='bold')
    ax1.set_xlabel('n_iterations_factor', fontsize=12)
    ax1.set_ylabel('Average Time (ms)', fontsize=12)
    ax1.legend(title='Weight')
    ax1.grid(True, which='both', linestyle='--', linewidth=0.5)
    output_path1 = os.path.join(output_dir, "fixed_n_performance_comparison.png")
    plt.savefig(output_path1, dpi=300, bbox_inches='tight')
    plt.close(fig1)
    print(f"Saved Fixed-N performance plot to {output_path1}")

    # Plot 2: Failure Rate Comparison
    fig2, ax2 = plt.subplots(figsize=(12, 8))
    for weight in sorted(fixed_n_df['Weight'].unique()):
        subset = fixed_n_df[fixed_n_df['Weight'] == weight]
        ax2.plot(subset['n_iter_factor'], subset['Failure Rate (%)'], marker='x', linestyle='--', label=f'Weight = {weight}')
    ax2.set_title('Fixed-N Failure Rate Comparison', fontsize=16, fontweight='bold')
    ax2.set_xlabel('n_iterations_factor', fontsize=12)
    ax2.set_ylabel('Failure Rate (%)', fontsize=12)
    ax2.legend(title='Weight')
    ax2.grid(True, which='both', linestyle='--', linewidth=0.5)
    output_path2 = os.path.join(output_dir, "fixed_n_failure_rate_comparison.png")
    plt.savefig(output_path2, dpi=300, bbox_inches='tight')
    plt.close(fig2)
    print(f"Saved Fixed-N failure rate plot to {output_path2}")

def plot_ctus_line_comparison(df, output_dir):
    '''Generates and saves simplified line plots for the CTUS algorithm where k_factor == att_factor.'''
    ctus_df = df[df['Algorithm'] == 'CTUS'].copy()
    if ctus_df.empty:
        print("No data found for CTUS algorithm.")
        return

    # Extract numeric factor values
    ctus_df['k_factor'] = ctus_df['Parameter 1'].str.replace('k_', '').astype(float)
    ctus_df['att_factor'] = ctus_df['Parameter 2'].str.replace('att_', '').astype(float)
    
    # Filter for the diagonal where k_factor equals att_factor
    diag_df = ctus_df[ctus_df['k_factor'] == ctus_df['att_factor']].copy()
    diag_df['factor'] = diag_df['k_factor']
    diag_df['Failure Rate (%)'] = 100.0 - diag_df['Success Rate (%)']

    if diag_df.empty:
        print("No data found for CTUS where k_factor == attempts_factor.")
        return

    plt.style.use('seaborn-v0_8-whitegrid')

    # Plot 1: Performance Comparison
    fig1, ax1 = plt.subplots(figsize=(12, 8))
    for weight in sorted(diag_df['Weight'].unique()):
        subset = diag_df[diag_df['Weight'] == weight]
        ax1.plot(subset['factor'], subset['Avg. Time (ms)'], marker='o', linestyle='-', label=f'Weight = {weight}')
    ax1.set_title('CTUS Performance Comparison (k_factor = attempts_factor)', fontsize=16, fontweight='bold')
    ax1.set_xlabel('Factor (k_factor = attempts_factor)', fontsize=12)
    ax1.set_ylabel('Average Time (ms)', fontsize=12)
    ax1.legend(title='Weight')
    ax1.grid(True, which='both', linestyle='--', linewidth=0.5)
    output_path1 = os.path.join(output_dir, "ctus_diagonal_performance_comparison.png")
    plt.savefig(output_path1, dpi=300, bbox_inches='tight')
    plt.close(fig1)
    print(f"Saved CTUS diagonal performance plot to {output_path1}")

    # Plot 2: Failure Rate Comparison
    fig2, ax2 = plt.subplots(figsize=(12, 8))
    for weight in sorted(diag_df['Weight'].unique()):
        subset = diag_df[diag_df['Weight'] == weight]
        ax2.plot(subset['factor'], subset['Failure Rate (%)'], marker='x', linestyle='--', label=f'Weight = {weight}')
    ax2.set_title('CTUS Failure Rate Comparison (k_factor = attempts_factor)', fontsize=16, fontweight='bold')
    ax2.set_xlabel('Factor (k_factor = attempts_factor)', fontsize=12)
    ax2.set_ylabel('Failure Rate (%)', fontsize=12)
    ax2.legend(title='Weight')
    ax2.grid(True, which='both', linestyle='--', linewidth=0.5)
    output_path2 = os.path.join(output_dir, "ctus_diagonal_failure_rate_comparison.png")
    plt.savefig(output_path2, dpi=300, bbox_inches='tight')
    plt.close(fig2)
    print(f"Saved CTUS diagonal failure rate plot to {output_path2}")

def main():
    '''Main function to run the visualization.'''
    csv_file = 'sampling_results_final.csv'
    output_dir = 'test_visualizations'

    if not os.path.exists(csv_file):
        print(f"Error: CSV file '{csv_file}' not found.")
        print("Please run the test first to generate the data.")
        return

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    try:
        df = pd.read_csv(csv_file)
    except Exception as e:
        print(f"Error reading CSV file: {e}")
        return

    plot_fixed_n_comparison(df, output_dir)
    plot_ctus_line_comparison(df, output_dir)

    print("\nVisualization script finished.")

if __name__ == "__main__":
    main()