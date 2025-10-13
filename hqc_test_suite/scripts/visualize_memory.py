import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
import os

# --- Configuration ---
script_dir = os.path.dirname(os.path.realpath(__file__))
DATA_FILES = {
    "CTUS": os.path.join(script_dir, "..", "data", "memory", "memory_ctus_benchmark_raw_data.csv"),
    "Fixed-N": os.path.join(script_dir, "..", "data", "memory", "memory_fixed-n_benchmark_raw_data.csv"),
    "Latest": os.path.join(script_dir, "..", "data", "memory", "memory_latest_benchmark_raw_data.csv"),
    "Original": os.path.join(script_dir, "..", "data", "memory", "memory_original_benchmark_raw_data.csv")
}

# The plot types you want to generate in the final report
PLOT_TYPES_TO_GENERATE = ["box_strip", "violin"]

# --- End Configuration ---

def load_and_prepare_data(file_mapping):
    """Loads all CSV files and combines them into a single DataFrame."""
    all_data = []
    print("Loading and processing data files...")
    for name, path in file_mapping.items():
        if not os.path.exists(path):
            print(f"Warning: Data file not found at '{path}'. Skipping.")
            continue
        try:
            df = pd.read_csv(path)
            df['implementation'] = name
            all_data.append(df)
            print(f" -> Successfully loaded {path}")
        except Exception as e:
            print(f"Error loading {path}: {e}")

    if not all_data:
        return None

    combined_df = pd.concat(all_data, ignore_index=True)
    combined_df['memory_mb'] = combined_df['memory_bytes'] / (1024 * 1024)
    
    hqc_order = ['HQC-128', 'HQC-192', 'HQC-256']
    op_order = ['keygen', 'encaps', 'decaps']
    combined_df['algorithm'] = pd.Categorical(combined_df['algorithm'], categories=hqc_order, ordered=True)
    combined_df['operation'] = pd.Categorical(combined_df['operation'], categories=op_order, ordered=True)

    return combined_df

def create_combined_plot(df, plot_type):
    """Creates a single image with 3 vertical subplots (one for each HQC level)."""
    hqc_levels = df['algorithm'].unique().categories
    
    print(f"\nGenerating combined {plot_type.replace('_', ' ')} plot...")

    # Create a figure with 3 vertical subplots, with a 16:12 aspect ratio.
    fig, axes = plt.subplots(nrows=3, ncols=1, figsize=(16, 12), sharex=True)
    fig.suptitle(f'Memory Usage Comparison', fontsize=20, fontweight='bold')

    for i, hqc_level in enumerate(hqc_levels):
        ax = axes[i]
        level_df = df[df['algorithm'] == hqc_level]

        if plot_type == "box_strip":
            sns.boxplot(data=level_df, x='operation', y='memory_mb', hue='implementation', ax=ax, palette="viridis", fliersize=0)
            sns.stripplot(data=level_df, x='operation', y='memory_mb', hue='implementation', ax=ax, dodge=True, jitter=0.1, alpha=0.4, size=3, legend=False, palette="viridis")
        
        elif plot_type == "violin":
            sns.violinplot(data=level_df, x='operation', y='memory_mb', hue='implementation', ax=ax, palette="viridis", inner="quartile", cut=0)

        ax.set_title(f'Results for {hqc_level}', fontsize=14)
        ax.set_ylabel('Memory (MB)', fontsize=12)
        ax.set_xlabel(None) # Remove individual x-labels
        if ax.get_legend() is not None:
            ax.get_legend().remove() # Remove individual legends

    # Create a single, shared legend for the entire figure, placed to the right
    handles, labels = axes[0].get_legend_handles_labels()
    unique_labels = {}
    for handle, label in zip(handles, labels):
        if label not in unique_labels:
            unique_labels[label] = handle
    # Changed loc and bbox_to_anchor to move legend to the top-right
    fig.legend(unique_labels.values(), unique_labels.keys(), title='Implementation', 
           bbox_to_anchor=(0.98, 0.98), loc='upper right', borderaxespad=0.1, 
           frameon=True, fancybox=True)
    # Set a single x-label for the bottom plot
    axes[-1].set_xlabel('Operation', fontsize=14)

    # Adjust layout to make space for suptitle and the shared legend
    plt.tight_layout(rect=[0, 0.03, 1, 0.95])
    
    output_dir = os.path.join(script_dir, "..", "results", "memory_charts")
    os.makedirs(output_dir, exist_ok=True)
    output_filename = os.path.join(output_dir, f'memory_result_{plot_type}.png')
    try:
        plt.savefig(output_filename, dpi=300)
        print(f" -> Successfully saved combined plot to {output_filename}")
    except Exception as e:
        print(f"Error saving plot {output_filename}: {e}")
    
    plt.close(fig)

def main():
    """Main function to load data and generate all requested plot types."""
    full_df = load_and_prepare_data(DATA_FILES)

    if full_df is None or full_df.empty:
        print("\nNo data was loaded. Exiting.")
        return

    for plot_type in PLOT_TYPES_TO_GENERATE:
        create_combined_plot(full_df, plot_type)
            
    print("\nAll plots generated.")

if __name__ == "__main__":
    main()