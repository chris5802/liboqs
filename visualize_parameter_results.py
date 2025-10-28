import pandas as pd
import matplotlib.pyplot as plt
import os

def plot_fixed_n(df, output_dir):
    """Generate Failure Rate plot for Fixed-N only (IEEE figure-ready)."""
    plt.style.use('seaborn-v0_8-whitegrid')

    # --- Process data ---
    fixed_n_df = df[df['Algorithm'] == 'Fixed-N'].copy()
    fixed_n_df['factor'] = fixed_n_df['Parameter 1'].str.replace('n_iter_', '').astype(float)
    fixed_n_df['Failure Rate (%)'] = 100.0 - fixed_n_df['Success Rate (%)']

    # --- Plot (A4/8 size ≈ 3.7×2.6 inch) ---
    fig, ax = plt.subplots(figsize=(3.7, 2.6))

    for weight in sorted(fixed_n_df['Weight'].unique()):
        subset = fixed_n_df[fixed_n_df['Weight'] == weight]
        ax.plot(subset['factor'], subset['Failure Rate (%)'],
                marker='o', linestyle='-', label=f'Weight = {weight}', linewidth=0.8, markersize=3)

    # --- Font & label setup ---
    plt.rcParams.update({
        'font.family': 'Times New Roman',
        'font.size': 7,
        'axes.labelsize': 7,
        'axes.titlesize': 7,
        'legend.fontsize': 6,
        'xtick.labelsize': 6,
        'ytick.labelsize': 6,
    })

    ax.set_title('Fixed-N Failure Rate', fontsize=7, fontweight='bold')
    ax.set_xlabel('Factor')
    ax.set_ylabel('Failure Rate (%)')
    ax.legend(title='Weight', frameon=False)
    ax.grid(True, which='both', linestyle='--', linewidth=0.3)

    plt.tight_layout(pad=0.5)
    output_path = os.path.join(output_dir, "fixed_n_failure_rate_ieee.png")
    plt.savefig(output_path, dpi=600)
    plt.close(fig)
    print(f"Saved Fixed-N plot to {output_path}")

def main():
    csv_file = 'sampling_results_hyperfine.csv'
    output_dir = 'test_visualizations'

    if not os.path.exists(csv_file):
        print(f"Error: CSV file '{csv_file}' not found.")
        return

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    df = pd.read_csv(csv_file)
    plot_fixed_n(df, output_dir)
    print("\nVisualization finished.")

if __name__ == "__main__":
    main()
