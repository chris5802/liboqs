#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Memory usage visualization + statistical testing for HQC implementations.

What this script does (publication-ready output):
- Loads all CSVs matching data/memory/memory_*_benchmark_raw_data.csv
- Builds violin (or box+strip) plots per security level (matching target image)
- Prints clean, structured tables (medians, describe)
- Runs one-sided Mann–Whitney U and Welch's t-tests vs baseline (less = better)
- Computes effect sizes: Cliff's delta (non-parametric) and Cohen's d
- Corrects for multiple comparisons with Benjamini–Hochberg FDR (q-values)
- Exports tidy CSVs of all key tables

Usage:
  python memory_analysis.py

Assumptions:
- Each CSV has at least: [algorithm, operation, memory_bytes]
- Filenames are memory_<impl>_benchmark_raw_data.csv (e.g., memory_ctus_benchmark_raw_data.csv)
- Baseline after title-casing is 'Original'. If your naming differs, change BASELINE below.
"""

import os
import glob
import numpy as np
import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
from scipy import stats

# =============================
# Configuration
# =============================
script_dir = os.path.dirname(os.path.realpath(__file__))
DATA_PATH_PATTERN = os.path.join(script_dir, "..", "data", "memory", "memory_*_benchmark_raw_data.csv")
PLOT_TYPES_TO_GENERATE = ["violin"]  # options: "violin", "box_strip"
BASELINE = "Original"  # must match the title-cased name after normalization

# =============================
# Pretty printing helpers
# =============================

def section(title: str) -> None:
    line = "=" * len(title)
    print(f"\n{title}\n{line}")


def subsection(title: str) -> None:
    line = "-" * len(title)
    print(f"\n{title}\n{line}")


def print_df(df: pd.DataFrame | None, title: str | None = None, floatfmt: str = "%.6f") -> None:
    if title:
        subsection(title)
    if df is None or df.empty:
        print("(no data)")
        return
    with pd.option_context(
        "display.max_rows", 200,
        "display.max_columns", 30,
        "display.width", 140,
        "display.float_format", lambda x: floatfmt % x,
    ):
        print(df.to_string())


# =============================
# Effect sizes & corrections
# =============================

def stars_from_p(p: float) -> str:
    if p < 0.001: return "***"
    if p < 0.01:  return "**"
    if p < 0.05:  return "*"
    return ""


def cliffs_delta(x: np.ndarray, y: np.ndarray) -> float:
    """Cliff's delta: P(X>Y) - P(X<Y), range [-1, 1]. Negative => x smaller (better)."""
    x = np.asarray(x); y = np.asarray(y)
    n, m = len(x), len(y)
    if n == 0 or m == 0:
        return np.nan
    x_sorted = np.sort(x)
    y_sorted = np.sort(y)
    i = j = 0
    gt = lt = 0
    # Two-pointer sweep
    while i < n and j < m:
        if x_sorted[i] > y_sorted[j]:
            gt += (n - i)
            j += 1
        elif x_sorted[i] < y_sorted[j]:
            lt += (m - j)
            i += 1
        else:
            # Advance both on ties
            i += 1
            j += 1
    return (gt - lt) / (n * m)


def cohens_d(x: np.ndarray, y: np.ndarray) -> float:
    """Welch's variant of Cohen's d. Negative => x smaller (better)."""
    x = np.asarray(x); y = np.asarray(y)
    nx, ny = len(x), len(y)
    if nx < 2 or ny < 2:
        return np.nan
    vx, vy = x.var(ddof=1), y.var(ddof=1)
    df = (nx - 1) + (ny - 1)
    if df <= 0:
        return np.nan
    sp = np.sqrt(((nx - 1) * vx + (ny - 1) * vy) / df)
    if sp == 0 or np.isnan(sp):
        return np.nan
    return (x.mean() - y.mean()) / sp


def fdr_bh(pvals: np.ndarray) -> np.ndarray:
    """Benjamini–Hochberg FDR. Returns q-values matching pvals shape."""
    p = np.asarray(pvals, dtype=float)
    m = p.size
    order = np.argsort(p)
    ranked = np.empty_like(p)
    # Compute raw BH values: p_i * m / i (i is 1-based rank in ascending p)
    raw = np.empty_like(p)
    for rank, idx in enumerate(order, start=1):
        raw[idx] = p[idx] * m / rank
    # Enforce monotonicity via reverse cumulative minimum
    cummin = np.minimum.accumulate(raw[order[::-1]])[::-1]
    ranked[order] = cummin
    return np.minimum(ranked, 1.0)


# =============================
# Data loading & plotting
# =============================

def load_and_prepare_data(path_pattern: str) -> pd.DataFrame:
    """Load all CSVs, annotate source, compute MB, and normalize source names."""
    all_data: list[pd.DataFrame] = []
    file_paths = glob.glob(path_pattern)

    if not file_paths:
        print(f"Warning: No data files found matching pattern '{path_pattern}'.")
        return pd.DataFrame()

    print("Loading and processing memory data files...")
    for path in file_paths:
        try:
            filename = os.path.basename(path)
            
            # **MODIFICATION**: Re-added the 'ctus' filter to exclude it.
            if "ctus" in filename.lower():
                print(f" -> Skipping file for 'ctus' implementation: {filename}")
                continue
                
            implementation_name = filename.replace("memory_", "").replace("_benchmark_raw_data.csv", "")
            
            # **MODIFICATION**: Mapped names to match your new request
            if implementation_name.lower() == "latest": # Changed from 'gates'
                source_name = "Latest" # Changed from 'GATES'
            elif implementation_name.lower() == "fixed-n":
                source_name = "Fixed-N"
            elif implementation_name.lower() == "original":
                source_name = "Original"
            else:
                source_name = implementation_name.title() # Fallback for any others

            df = pd.read_csv(path)
            df["source"] = source_name
            all_data.append(df)
            print(f" -> Successfully loaded {path} as '{source_name}'")
        except Exception as e:
            print(f"Error loading {path}: {e}")

    if not all_data:
        return pd.DataFrame()

    full_df = pd.concat(all_data, ignore_index=True)
    
    # Using MB
    full_df["memory_mb"] = full_df["memory_bytes"] / (1024.0 * 1024.0)
    
    return full_df

def create_combined_plot(data: pd.DataFrame, plot_type: str) -> None:
    """Create a grid of violin plots for memory usage, faceted by operation and algorithm."""
    if data.empty:
        print("Cannot create plot: No data.")
        return

    print(f"\nCreating '{plot_type}' plot grid (target image format)...")
    plt.style.use('seaborn-v0_8-whitegrid')

    # Sort order for rows (algorithms)
    row_order = sorted(data["algorithm"].unique())
    # Set order for X-axis (operations)
    op_order = ["keygen", "encaps", "decaps"]
    
    # **MODIFICATION**: Updated hue_order to match your requested sort
    hue_order = ["Original", "Latest", "Fixed-N"] 

    # Ensure all expected operations are in the data to avoid errors
    op_order = [op for op in op_order if op in data["operation"].unique()]
    # Ensure all expected sources are in the data to avoid errors
    hue_order = [src for src in hue_order if src in data["source"].unique()]

    if plot_type == "violin":
        g = sns.catplot(
            data=data,
            x="operation",      
            y="memory_mb",      
            hue="source",         
            row="algorithm",      
            row_order=row_order,
            order=op_order,       
            hue_order=hue_order,  # This now uses the new order
            kind="violin",
            cut=0,
            inner="quartile",   
            sharey=False,       
            height=3,           
            aspect=2.5,         
            palette="viridis",
            legend_out=True
        )
    elif plot_type == "box_strip":
        g = sns.catplot(
            data=data,
            x="operation",
            y="memory_mb",
            hue="source",
            row="algorithm",
            row_order=row_order,
            order=op_order,
            hue_order=hue_order,  # This now uses the new order
            kind="box",
            showfliers=False,
            sharey=False,       
            height=3,
            aspect=2.5,
            palette="viridis",
            legend_out=True
        )
    else:
        print(f"Unsupported plot type: {plot_type}")
        return

    g.fig.suptitle("Memory Usage Comparison", fontsize=20, y=1.03)
    
    g.set_axis_labels("Operation", "Memory ")
    g.set_titles(row_template="Results for {row_name}", col_template=None)
    
    # Set legend title (as requested in previous step)
    g.legend.set_title('Algorithm')
    
    # Move legend to top-right corner (as requested in previous step)
    sns.move_legend(g, "upper right")
    
    # Let plot fill space (as requested in previous step)
    g.fig.tight_layout() 

    output_dir = os.path.join(script_dir, "..", "results", "memory_charts")
    os.makedirs(output_dir, exist_ok=True)
    output_filename = os.path.join(output_dir, f"memory_result_{plot_type}_by_level.png")

    try:
        g.savefig(output_filename, dpi=300)
        print(f" -> Successfully saved plot to {output_filename}")
    except Exception as e:
        print(f"Error saving plot {output_filename}: {e}")

    plt.close(g.fig)

def create_combined_plot_ieee_final_v7(data: pd.DataFrame) -> None:
    """
    IEEE-ready violin plot (A4/8 size, Times New Roman 7pt, top-right legend).
    Maintains clean proportion and readability for publication figures.
    """

    if data.empty:
        print("Cannot create IEEE plot: No data.")
        return

    import seaborn as sns
    import matplotlib.pyplot as plt
    import os

    print("\nCreating IEEE publication violin plot (Times 7pt, A4/8 size)...")
    plt.style.use('seaborn-v0_8-whitegrid')

    # === 字體設定 (Times New Roman, 7pt) ===
    plt.rcParams.update({
        'font.family': 'Times New Roman',
        'font.size': 7,
        'axes.labelsize': 7,
        'axes.titlesize': 7,
        'legend.fontsize': 7,
        'xtick.labelsize': 7,
        'ytick.labelsize': 7,
    })

    # === 資料順序設定 ===
    row_order = sorted(data["algorithm"].unique())
    op_order = ["keygen", "encaps", "decaps"]
    hue_order = [src for src in ["Original", "Latest", "Fixed-N"] if src in data["source"].unique()]

    # === 畫圖 ===
    g = sns.catplot(
        data=data,
        x="operation",
        y="memory_mb",
        hue="source",
        row="algorithm",
        row_order=row_order,
        order=op_order,
        hue_order=hue_order,
        kind="violin",
        cut=0,
        inner="quartile",
        sharey=False,
        height=0.9,        # 每列子圖高度
        aspect=1.4,         # 每列寬高比例
        width=0.6,
        palette="viridis",
        legend_out=False    # 把 legend 放圖內
    )

    # === 標題與標籤 ===
    g.fig.suptitle("Memory Usage Comparison (IEEE Compact)", fontsize=7, fontweight="bold", y=1.02)
    g.set_axis_labels("Operation", "Memory")
    g.set_titles(row_template="{row_name}", col_template=None)

    # === Legend ===
    g._legend.set_title("Implementation")
    # 將 legend 放右上角
    g._legend.set_bbox_to_anchor((0.98, 0.98))  # 控制相對位置 (右上)
    g._legend._loc = 2  # upper left inside legend box
    for text in g._legend.texts:
        text.set_fontsize(7)

    # === Layout 微調 ===
    g.fig.subplots_adjust(top=0.9, hspace=0.45, left=0.18, right=0.95, bottom=0.18)
    g.fig.set_size_inches(3.7, 2.6)  # A4 八分之一大小
    sns.despine(trim=True)

    # === 儲存 ===
    output_dir = os.path.join(script_dir, "..", "results", "memory_charts")
    os.makedirs(output_dir, exist_ok=True)
    out_path = os.path.join(output_dir, "memory_ieee_violin_by_level_v7.png")

    g.savefig(out_path, dpi=600, bbox_inches="tight")
    plt.close(g.fig)

    print(f"✅ Saved IEEE 7pt violin plot to {out_path}")

# =============================
# Statistical tests for memory
# =============================

def run_memory_tests(full_df: pd.DataFrame, baseline: str = BASELINE) -> pd.DataFrame | None:
    """For each (algorithm, operation), compare each source vs baseline with one-sided tests.

    Hypothesis: comparison uses LESS memory than baseline (alternative='less').
    Returns a tidy DataFrame indexed by (algorithm, operation, comparison).
    """
    if full_df.empty:
        return None

    df = full_df.copy()
    df["source"] = df["source"].str.strip()

    algorithms = sorted(df["algorithm"].unique())
    operations = sorted(df["operation"].unique())
    sources = sorted(df["source"].unique())

    if baseline not in sources:
        print(f"Baseline '{baseline}' not found in sources: {sources}")
        return None

    rows: list[dict] = []
    for alg in algorithms:
        for op in operations:
            # **MODIFICATION**: Use memory_mb
            base_vals = df[(df["algorithm"] == alg) & (df["operation"] == op) & (df["source"] == baseline)]["memory_mb"].values
            if base_vals.size == 0:
                continue
            for src in sources:
                if src == baseline:
                    continue
                # **MODIFICATION**: Use memory_mb
                comp_vals = df[(df["algorithm"] == alg) & (df["operation"] == op) & (df["source"] == src)]["memory_mb"].values
                if comp_vals.size == 0:
                    continue

                # Non-parametric: Mann–Whitney U (one-sided: comp < base)
                mwu_stat, mwu_p = stats.mannwhitneyu(comp_vals, base_vals, alternative='less')
                # Parametric: Welch's t-test (one-sided)
                t_stat, t_p = stats.ttest_ind(comp_vals, base_vals, alternative='less', equal_var=False)
                # Effect sizes
                delta = cliffs_delta(comp_vals, base_vals)  # negative => comp smaller (better)
                d = cohens_d(comp_vals, base_vals)          # negative => comp smaller (better)

                rows.append({
                    "algorithm": alg,
                    "operation": op,
                    "comparison": f"{src} vs {baseline}",
                    "src": src,
                    "MWU_p": float(mwu_p),
                    "T_p": float(t_p),
                    "CliffsDelta": float(delta) if delta == delta else np.nan,
                    "Cohens_d": float(d) if d == d else np.nan,
                })

    out = pd.DataFrame(rows)
    if out.empty:
        return out

    # FDR per (algorithm, operation)
    out["MWU_q"] = np.nan
    out["T_q"] = np.nan
    for (alg, op), g in out.groupby(["algorithm", "operation"]):
        idx = g.index
        out.loc[idx, "MWU_q"] = fdr_bh(g["MWU_p"].values)
        out.loc[idx, "T_q"] = fdr_bh(g["T_p"].values)

    # Significance stars by q-values
    out["MWU_sig"] = out["MWU_q"].apply(stars_from_p)
    out["T_sig"] = out["T_q"].apply(stars_from_p)

    # Tidy pivot for printing and CSV
    tidy = (out
            .sort_values(["algorithm", "operation", "src"])\
            .set_index(["algorithm", "operation", "comparison"])\
            [["MWU_p", "MWU_q", "MWU_sig", "T_p", "T_q", "T_sig", "CliffsDelta", "Cohens_d"]]
           )

    tables_dir = os.path.join(script_dir, "..", "results", "tables")
    os.makedirs(tables_dir, exist_ok=True)
    csv_path = os.path.join(tables_dir, "memory_stats_tests.csv")
    tidy.to_csv(csv_path)
    print(f"Saved memory statistical test table to: {csv_path}")

    return tidy


# =============================
# Main
# =============================

def main() -> None:
    full_df = load_and_prepare_data(DATA_PATH_PATTERN)
    if full_df.empty:
        print("No data loaded. Exiting.")
        return

    # 1) Plots
    for plot_type in PLOT_TYPES_TO_GENERATE:
        create_combined_plot(full_df, plot_type)
        create_combined_plot_ieee_final_v7(full_df)

    # 2) Summary statistics grouped by level
    # **MODIFICATION**: Changed titles to Megabytes
    section("Memory Usage Statistics (Megabytes)")

    # **MODIFICATION**: Use memory_mb
    median_memory = full_df.groupby(["source", "algorithm", "operation"])['memory_mb'].median().unstack()
    print_df(median_memory.round(2), title="Median Memory Usage (MB) per Security Level")

    # **MODIFICATION**: Use memory_mb
    summary_stats = full_df.groupby(["source", "algorithm", "operation"])['memory_mb'].describe()
    print_df(summary_stats.round(2), title="Full Summary Statistics (MB) per Security Level")

    # Export summary CSVs
    tables_dir = os.path.join(script_dir, "..", "results", "tables")
    os.makedirs(tables_dir, exist_ok=True)
    median_csv = os.path.join(tables_dir, "memory_median_usage.csv")
    desc_csv = os.path.join(tables_dir, "memory_describe_stats.csv")
    median_memory.round(4).to_csv(median_csv)
    summary_stats.round(4).to_csv(desc_csv)
    print(f"Saved tables to: {tables_dir}")

    # 3) Statistical tests vs baseline (one-sided: less = better)
    section("Statistical Tests on Memory (one-sided: less = better)")
    test_table = run_memory_tests(full_df, baseline=BASELINE)
    if test_table is not None and not test_table.empty:
        show = test_table.copy()
        for c in ["MWU_p", "MWU_q", "T_p", "T_q", "CliffsDelta", "Cohens_d"]:
            show[c] = show[c].astype(float).round(6)
        print_df(show, title="(algorithm, operation) → comparison stats")


if __name__ == "__main__":
    main()