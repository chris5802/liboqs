#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
HQC performance visualization and statistical analysis (tidy console output).

This script preserves your original logic (plots + summary stats) and adds:
- Structured, readable console output with section dividers
- Side-by-side p-value tables for Mann–Whitney U and Welch's t-test
- Significance stars (***, **, *)
- CSV exports for all key tables
- Optional Markdown report export via --markdown

Usage:
  python visualize_performance.py <level> [--markdown]
  <level> in {128, 192, 256}

Notes:
- We keep seaborn and your plotting style intact.
- Statistical tests use a one-sided hypothesis (alternative='less'): comparison < baseline (faster).
"""

import argparse
import glob
import os
import sys
import textwrap

import matplotlib.pyplot as plt
import pandas as pd
import seaborn as sns
from scipy import stats

# =============================
# Pretty printing / formatting
# =============================

def section(title: str) -> None:
    """Print a top-level console section with an underline."""
    line = "=" * len(title)
    print(f"\n{title}\n{line}")


def subsection(title: str) -> None:
    """Print a sub-section with a dashed underline."""
    line = "-" * len(title)
    print(f"\n{title}\n{line}")


def stars_from_p(p: float) -> str:
    """Return significance stars for a given p-value."""
    if p < 0.001:
        return "***"
    if p < 0.01:
        return "**"
    if p < 0.05:
        return "*"
    return ""


def print_df(df: pd.DataFrame, title: str | None = None, floatfmt: str = "%.6f", int_as_int: bool = True) -> None:
    """Pretty-print a pandas DataFrame with optional title and integer-friendly formatting."""
    if title:
        subsection(title)

    if df is None:
        print("(no data)")
        return

    # Attempt to display integer-looking float columns as integers
    df_to_show = df.copy()
    if int_as_int:
        for col in df_to_show.columns:
            try:
                s = df_to_show[col]
                if pd.api.types.is_float_dtype(s) and (s.dropna() % 1 == 0).all():
                    df_to_show[col] = s.astype("Int64")
            except Exception:
                # Be forgiving if a column doesn't support modulus or casting
                pass

    with pd.option_context(
        "display.max_rows", 200,
        "display.max_columns", 20,
        "display.width", 120,
        "display.float_format", lambda x: floatfmt % x,
    ):
        print(df_to_show.to_string(index=True))


# =============================
# Plotting (preserve your style)
# =============================

def plot_individual_operations(df: pd.DataFrame, level: str, output_dir: str, source_order: list[str]) -> None:
    """Generate 1x3 boxplots for keypair / encaps / decaps with independent y-axes (log scale)."""
    print("Generating performance comparison plot with independent y-axis subplots...")

    sns.set_style("whitegrid")
    operations = ["keypair", "encaps", "decaps"]
    fig, axes = plt.subplots(1, len(operations), figsize=(24, 8), sharey=False)
    fig.suptitle(f"HQC-{level} Performance Comparison", fontsize=20, fontweight="bold")

    for i, op in enumerate(operations):
        ax = axes[i]
        op_data = df[df["operation"] == op]

        sns.boxplot(
            x="source",
            y="cycles",
            hue="source",
            data=op_data,
            ax=ax,
            palette="viridis",
            legend=False,
            order=source_order,
        )

        ax.set_title(f"Operation: {op}", fontsize=16, fontweight="bold")
        ax.set_xlabel("Data Source", fontsize=12)
        ax.set_ylabel("CPU Cycles ", fontsize=12)

        ax.set_yscale("log")
        ax.tick_params(axis="x", labelsize=12, rotation=45)
        ax.tick_params(axis="y", labelsize=10)

    plt.tight_layout(rect=[0, 0.03, 1, 0.95])
    output_filename = os.path.join(output_dir, f"hqc{level}_performance.png")
    plt.savefig(output_filename, dpi=300, bbox_inches="tight")
    print(f"Successfully created the individual plot and saved it as '{output_filename}'")

def plot_individual_operations_ieee(df: pd.DataFrame, level: str, output_dir: str, source_order: list[str]) -> None:
    """
    Generate IEEE-ready boxplots (with and without outliers removed)
    for keypair, encaps, and decaps.
    Keeps the original plotting logic intact — this is an additional compact version.
    """
    print("Generating compact IEEE-style performance plots (with and without outliers)...")

    import seaborn as sns
    import matplotlib.pyplot as plt
    import os

    sns.set_style("whitegrid")

    # === Times New Roman + 7pt for IEEE figure ===
    plt.rcParams.update({
        'font.family': 'Times New Roman',
        'font.size': 7,
        'axes.labelsize': 7,
        'axes.titlesize': 7,
        'legend.fontsize': 6,
        'xtick.labelsize': 6,
        'ytick.labelsize': 6,
    })

    operations = ["keypair", "encaps", "decaps"]

    # Helper function: remove outliers via IQR
    def remove_outliers_iqr(data):
        q1 = data["cycles"].quantile(0.25)
        q3 = data["cycles"].quantile(0.75)
        iqr = q3 - q1
        lower, upper = q1 - 1.5 * iqr, q3 + 1.5 * iqr
        return data[(data["cycles"] >= lower) & (data["cycles"] <= upper)]

    # --- A4 1/8 size (3.7×2.6 inch) ---
    figsize_single = (3.7 * len(operations) / 3, 2.6)

    # === (1) 原始資料版本（淡灰 outlier） ===
    fig, axes = plt.subplots(1, len(operations), figsize=figsize_single, sharey=False)
    fig.suptitle(f"HQC-{level} Performance (All Data)", fontsize=7, fontweight="bold")

    for i, op in enumerate(operations):
        ax = axes[i] if len(operations) > 1 else axes
        op_data = df[df["operation"] == op]
        sns.boxplot(
            x="source",
            y="cycles",
            hue="source",
            data=op_data,
            ax=ax,
            palette="viridis",
            legend=False,
            order=source_order,
            linewidth=0.5,
            flierprops={'marker': 'o', 'markerfacecolor': 'gray', 'alpha': 0.25, 'markersize': 2}  # 淡灰點
        )
        ax.set_title(op.capitalize(), fontsize=7)
        ax.set_xlabel("")
        ax.set_ylabel("CPU Cycles " if i == 0 else "")
        ax.set_yscale("log")
        ax.tick_params(axis="x", labelrotation=45)
        ax.grid(True, linestyle="--", linewidth=0.3)

    plt.tight_layout(pad=0.4)
    output_all = os.path.join(output_dir, f"hqc{level}_ieee_performance_all.png")
    plt.savefig(output_all, dpi=600, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved IEEE version (all data) to {output_all}")

    # === (2) 去離群值版本（完全不顯示 outlier） ===
    df_no_outlier = df.groupby(["source", "operation"], group_keys=False).apply(remove_outliers_iqr)

    fig, axes = plt.subplots(1, len(operations), figsize=figsize_single, sharey=False)
    fig.suptitle(f"HQC-{level} Performance", fontsize=7, fontweight="bold")

    for i, op in enumerate(operations):
        ax = axes[i] if len(operations) > 1 else axes
        op_data = df_no_outlier[df_no_outlier["operation"] == op]
        sns.boxplot(
            x="source",
            y="cycles",
            hue="source",
            data=op_data,
            ax=ax,
            palette="viridis",
            legend=False,
            order=source_order,
            linewidth=0.5,
            showfliers=False  # 不畫 outlier
        )
        ax.set_title(op.capitalize(), fontsize=7)
        ax.set_xlabel("")
        ax.set_ylabel("CPU Cycles" if i == 0 else "")
        ax.set_yscale("log")
        ax.tick_params(axis="x", labelrotation=45)
        ax.grid(True, linestyle="--", linewidth=0.3)

    plt.tight_layout(pad=0.4)
    output_no_outliers = os.path.join(output_dir, f"hqc{level}_ieee_performance_no_outliers.png")
    plt.savefig(output_no_outliers, dpi=600, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved IEEE version (outliers removed) to {output_no_outliers}")

def plot_total_combined_ieee(df: pd.DataFrame, level: str, output_dir: str, source_order: list[str]) -> None:
    """
    Generate IEEE-ready compact boxplot for TOTAL (keypair + encaps + decaps).
    Outputs two versions: all data and outlier-removed.
    """
    print("Generating IEEE-style TOTAL performance plots (with and without outliers)...")

    import seaborn as sns
    import matplotlib.pyplot as plt
    import os

    sns.set_style("whitegrid")

    # Font & style settings
    plt.rcParams.update({
        'font.family': 'Times New Roman',
        'font.size': 7,
        'axes.labelsize': 7,
        'axes.titlesize': 7,
        'legend.fontsize': 6,
        'xtick.labelsize': 6,
        'ytick.labelsize': 6,
    })

    # Helper: remove outliers by IQR
    def remove_outliers_iqr(data):
        q1 = data["cycles"].quantile(0.25)
        q3 = data["cycles"].quantile(0.75)
        iqr = q3 - q1
        lower, upper = q1 - 1.5 * iqr, q3 + 1.5 * iqr
        return data[(data["cycles"] >= lower) & (data["cycles"] <= upper)]

    # Compute total cycles per run (keypair + encaps + decaps)
    total_df = df.groupby(["source", "run_id"])["cycles"].sum().reset_index()

    # Figure size for IEEE small plot
    figsize_single = (3.7, 2.6)

    # === (1) All data (淡灰 outlier) ===
    fig, ax = plt.subplots(figsize=figsize_single)
    fig.suptitle(f"HQC-{level} Total Performance (All Data)", fontsize=7, fontweight="bold")

    sns.boxplot(
        x="source",
        y="cycles",
        hue="source",
        data=total_df,
        ax=ax,
        palette="viridis",
        legend=False,
        order=source_order,
        linewidth=0.5,
        flierprops={'marker': 'o', 'markerfacecolor': 'gray', 'alpha': 0.25, 'markersize': 2}
    )

    ax.set_xlabel("")
    ax.set_ylabel("Total CPU Cycles")
    ax.set_yscale("log")
    ax.tick_params(axis="x", labelrotation=45)
    ax.grid(True, linestyle="--", linewidth=0.3)

    plt.tight_layout(pad=0.4)
    output_all = os.path.join(output_dir, f"hqc{level}_ieee_total_all.png")
    plt.savefig(output_all, dpi=600, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved IEEE total plot (all data) to {output_all}")

    # === (2) Outlier-removed version ===
    total_no_outlier = total_df.groupby("source", group_keys=False).apply(remove_outliers_iqr)

    fig, ax = plt.subplots(figsize=figsize_single)
    fig.suptitle(f"HQC-{level}  Performance ", fontsize=7, fontweight="bold")

    sns.boxplot(
        x="source",
        y="cycles",
        hue="source",
        data=total_no_outlier,
        ax=ax,
        palette="viridis",
        legend=False,
        order=source_order,
        linewidth=0.5,
        showfliers=False  # 不畫 outlier
    )

    ax.set_xlabel("")
    ax.set_ylabel("Total CPU Cycles ")
    ax.set_yscale("log")
    ax.tick_params(axis="x", labelrotation=45)
    ax.grid(True, linestyle="--", linewidth=0.3)

    plt.tight_layout(pad=0.4)
    output_no_outliers = os.path.join(output_dir, f"hqc{level}_ieee_total_no_outliers.png")
    plt.savefig(output_no_outliers, dpi=600, bbox_inches="tight")
    plt.close(fig)
    print(f"Saved IEEE total plot (outliers removed) to {output_no_outliers}")


def plot_total_comparison(df: pd.DataFrame, level: str, output_dir: str, source_order: list[str]) -> None:
    """Generate a square boxplot for TOTAL cycles (keypair + encaps + decaps)."""
    print(f"\nGenerating HQC-{level} TOTAL performance plot...")

    sns.set_style("whitegrid")

    fig, ax = plt.subplots(1, 1, figsize=(8, 8))
    fig.suptitle(
        f"HQC-{level} Total Performance\n(keypair + encaps + decaps)",
        fontsize=20,
        fontweight="bold",
    )

    sns.boxplot(
        x="source",
        y="cycles",
        hue="source",
        data=df,
        ax=ax,
        palette="viridis",
        legend=False,
        order=source_order,
    )

    ax.set_title("Comparison of Total Cycles", fontsize=16)
    ax.set_xlabel("Data Source", fontsize=12)
    ax.set_ylabel("Total CPU Cycles ", fontsize=12)

    ax.set_yscale("log")
    ax.tick_params(axis="x", labelsize=12, rotation=45)
    ax.tick_params(axis="y", labelsize=10)

    plt.tight_layout(rect=[0, 0.03, 1, 0.93])
    output_filename = os.path.join(output_dir, f"hqc{level}_total_performance.png")
    plt.savefig(output_filename, dpi=300, bbox_inches="tight")
    print(f"Successfully created the total plot and saved it as '{output_filename}'")


# =============================
# Improvement summary (median-based)
# =============================

def print_performance_improvement(
    median_cycles: pd.DataFrame,
    total_summary_stats: pd.DataFrame,
    source_order: list[str],
) -> None:
    """Print % improvement vs baseline using medians for per-operation and total cycles."""
    print("\n\n--- Performance Improvement vs Baseline (Median) ---")

    if not source_order or len(source_order) < 2:
        print("Not enough data sources for comparison.")
        return

    baseline_source = source_order[0]
    comparison_sources = source_order[1:]

    print(f"Baseline for comparison: '{baseline_source}'")
    print("Positive (+) values mean FASTER (fewer cycles).")
    print("Negative (-) values mean SLOWER (more cycles).\n")

    try:
        baseline_medians = median_cycles.loc[baseline_source]
        baseline_total_median = total_summary_stats.loc[baseline_source]["50%"]

        for comp_source in comparison_sources:
            print(f"--- Comparison: '{comp_source}' vs '{baseline_source}' ---")

            # Per-operation improvements
            if comp_source in median_cycles.index:
                comp_medians = median_cycles.loc[comp_source]
                for op in median_cycles.columns:
                    baseline_val = baseline_medians[op]
                    comp_val = comp_medians[op]
                    if pd.isna(baseline_val) or pd.isna(comp_val) or baseline_val == 0:
                        print(f"  - {op:<7}: N/A (Missing data or baseline is zero)")
                        continue
                    improvement_pct = (baseline_val - comp_val) / baseline_val * 100
                    print(f"  - {op:<7}: {improvement_pct:+.2f}%")
            else:
                print(f"  - Individual Ops: No data for '{comp_source}'")

            # Total cycles improvements
            if comp_source in total_summary_stats.index:
                comp_total_median = total_summary_stats.loc[comp_source]["50%"]
                if pd.isna(baseline_total_median) or pd.isna(comp_total_median) or baseline_total_median == 0:
                    print(f"  - TOTAL  : N/A (Missing data or baseline is zero)")
                else:
                    total_improvement_pct = (
                        (baseline_total_median - comp_total_median) / baseline_total_median * 100
                    )
                    print(f"  - TOTAL  : {total_improvement_pct:+.2f}%")
            else:
                print(f"  - TOTAL  : No data for '{comp_source}'")

            print("")

    except KeyError as e:
        print(f"Error: Could not find source '{e}' in the summary tables. Cannot calculate improvements.")
    except Exception as e:
        print(f"An error occurred during improvement calculation: {e}")


# =============================
# Statistical tests (return tables)
# =============================

def run_statistical_tests(
    combined_df: pd.DataFrame, total_cycles_df: pd.DataFrame, source_order: list[str]
) -> tuple[pd.DataFrame | None, pd.DataFrame | None]:
    """Run MWU and Welch's t-tests; return p-value tables for ops and totals.

    Returns
    -------
    op_table : pd.DataFrame | None
        Multi-index (operation, comparison) with columns [MWU_p, MWU_sig, T_p, T_sig].
    total_table : pd.DataFrame | None
        Index = comparison, columns same as above.
    """
    section("--- Statistical Significance Tests")

    if not source_order or len(source_order) < 2:
        print("Not enough data sources to perform statistical comparison.")
        return None, None

    baseline_source = source_order[0]
    comparison_sources = source_order[1:]

    print(f"Baseline for comparison: '{baseline_source}'")
    print("Hypothesis: Comparison source cycles are *less than* baseline (i.e., faster).")
    print("Significance level (alpha) = 0.05")

    operations = list(combined_df["operation"].unique())

    op_records: list[tuple] = []  # (operation, comp, MWU_p, MWU_sig, T_p, T_sig)
    total_records: list[tuple] = []  # (comp, MWU_p, MWU_sig, T_p, T_sig)

    # Individual operations
    subsection("Individual Operation Tests")
    for op in operations:
        print(f"\nOperation: {op}")
        base = combined_df[
            (combined_df["source"] == baseline_source) & (combined_df["operation"] == op)
        ]["cycles"]

        for comp in comparison_sources:
            comp_vals = combined_df[
                (combined_df["source"] == comp) & (combined_df["operation"] == op)
            ]["cycles"]

            if comp_vals.empty or base.empty:
                print(f"  - {comp} vs {baseline_source}: No data for one or both sources")
                continue

            # Mann–Whitney U (one-sided: comp < base)
            mwu_stat, mwu_p = stats.mannwhitneyu(comp_vals, base, alternative="less")
            mwu_tag = "SIGNIFICANT (Faster)" if mwu_p < 0.05 else "Not Significant"
            if mwu_p > 0.99:
                mwu_tag = "SIGNIFICANT (Slower)"

            # Welch's t-test (one-sided: comp < base)
            t_stat, t_p = stats.ttest_ind(comp_vals, base, alternative="less", equal_var=False)
            t_tag = "SIGNIFICANT (Faster)" if t_p < 0.05 else "Not Significant"
            if t_p > 0.99:
                t_tag = "SIGNIFICANT (Slower)"

            print(f"  - {comp} vs {baseline_source}: MWU p={mwu_p:.6f} ({mwu_tag})")
            print(f"      [t-test] p={t_p:.6f} ({t_tag})")

            op_records.append((op, comp, mwu_p, stars_from_p(mwu_p), t_p, stars_from_p(t_p)))

    # Total cycles
    subsection("Total Cycles Tests (keypair + encaps + decaps)")
    base_total = total_cycles_df[total_cycles_df["source"] == baseline_source]["cycles"]

    for comp in comparison_sources:
        comp_total = total_cycles_df[total_cycles_df["source"] == comp]["cycles"]
        if comp_total.empty or base_total.empty:
            print(f"  - {comp} vs {baseline_source}: No data for one or both sources")
            continue

        mwu_stat, mwu_p = stats.mannwhitneyu(comp_total, base_total, alternative="less")
        res = "SIGNIFICANT (Faster)" if mwu_p < 0.05 else "Not Significant"
        if mwu_p > 0.99:
            res = "SIGNIFICANT (Slower)"
        print(f"  - {comp} vs {baseline_source}: MWU p={mwu_p:.6f} ({res})")

        t_stat, t_p = stats.ttest_ind(comp_total, base_total, alternative="less", equal_var=False)

        total_records.append((comp, mwu_p, stars_from_p(mwu_p), t_p, stars_from_p(t_p)))

    # Assemble dataframes
    op_table = (
        pd.DataFrame(op_records, columns=["operation", "comparison", "MWU_p", "MWU_sig", "T_p", "T_sig"]).set_index(["operation", "comparison"]) if op_records else None
    )
    total_table = (
        pd.DataFrame(total_records, columns=["comparison", "MWU_p", "MWU_sig", "T_p", "T_sig"]).set_index("comparison") if total_records else None
    )

    return op_table, total_table

def compute_outlier_stats(df: pd.DataFrame) -> pd.DataFrame:
    """
    Compute outlier count and percentage per (source, operation) using IQR method.
    Returns a DataFrame with columns: count, outlier_count, outlier_pct.
    """
    records = []
    grouped = df.groupby(["source", "operation"])

    for (src, op), subdf in grouped:
        q1 = subdf["cycles"].quantile(0.25)
        q3 = subdf["cycles"].quantile(0.75)
        iqr = q3 - q1
        lower = q1 - 1.5 * iqr
        upper = q3 + 1.5 * iqr

        total = len(subdf)
        outliers = subdf[(subdf["cycles"] < lower) | (subdf["cycles"] > upper)]
        outlier_count = len(outliers)
        outlier_pct = (outlier_count / total) * 100 if total > 0 else 0

        records.append((src, op, total, outlier_count, outlier_pct))

    result = pd.DataFrame(
        records, columns=["source", "operation", "count", "outlier_count", "outlier_pct"]
    ).set_index(["source", "operation"])

    return result


# =============================
# Markdown report builder (optional)
# =============================

def format_md_table(df: pd.DataFrame) -> str:
    """Render a DataFrame as Markdown, falling back to a code block if needed."""
    if df is None:
        return "(no data)"
    try:
        return df.to_markdown()
    except Exception:
        return "```\n" + df.to_string() + "\n```"


def build_markdown_report(
    level: str,
    out_dir: str,
    median_cycles: pd.DataFrame,
    summary_stats: pd.DataFrame,
    total_summary_stats: pd.DataFrame,
    op_pvals: pd.DataFrame | None,
    total_pvals: pd.DataFrame | None,
) -> str:
    """Create a concise Markdown report and save it to the reports directory."""
    lines: list[str] = []
    lines.append(f"# HQC-{level} Performance Report\n")
    lines.append("## Median CPU Cycles per Operation\n")
    lines.append(format_md_table(median_cycles))

    lines.append("\n## Operation Describe (count/mean/std/min/25%/50%/75%/max)\n")
    lines.append(format_md_table(summary_stats))

    lines.append("\n## Total Cycles Describe\n")
    lines.append(format_md_table(total_summary_stats))

    if op_pvals is not None:
        tmp = op_pvals.copy()
        tmp["MWU_p"] = tmp["MWU_p"].round(6)
        tmp["T_p"] = tmp["T_p"].round(6)
        lines.append("\n## P-values (Operations)\n")
        lines.append(format_md_table(tmp))

    if total_pvals is not None:
        tmp = total_pvals.copy()
        tmp["MWU_p"] = tmp["MWU_p"].round(6)
        tmp["T_p"] = tmp["T_p"].round(6)
        lines.append("\n## P-values (Total)\n")
        lines.append(format_md_table(tmp))

    md = "\n\n".join(lines)
    md_dir = os.path.join(out_dir, "..", "reports")
    os.makedirs(md_dir, exist_ok=True)
    md_path = os.path.join(md_dir, f"hqc{level}_report.md")
    with open(md_path, "w", encoding="utf-8") as f:
        f.write(md)
    print(f"\nMarkdown report saved to: {md_path}")
    return md_path


# =============================
# CLI args
# =============================

def get_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Visualize HQC performance and run statistical analyses.")
    parser.add_argument("level", choices=["128", "192", "256"], help="HQC security level")
    parser.add_argument(
        "--markdown",
        action="store_true",
        help="Export a concise Markdown report to results/reports/",
    )
    return parser.parse_args()


# =============================
# Main
# =============================

def main() -> None:
    args = get_args()
    level = args.level

    # Resolve script directory robustly
    try:
        script_dir = os.path.dirname(os.path.realpath(__file__))
    except NameError:
        script_dir = os.getcwd()

    print(f"--- Generating visualization for HQC-{level} ---")

    # Discover CSV files
    search_path = os.path.join(script_dir, "..", "data", "performance", f"hqc{level}_*_data.csv")
    file_paths = glob.glob(search_path)

    if not file_paths:
        print(f"Warning: No data files found matching '{search_path}'. Exiting.")
        sys.exit(0)

    print(f"Found data files: {file_paths}")

    # Load & combine
    data_frames: list[pd.DataFrame] = []
    for f_path in file_paths:
        try:
            df = pd.read_csv(f_path)
            source_name = (
                os.path.basename(f_path)
                .replace(f"hqc{level}_", "")
                .replace("_data.csv", "")
            )
            df["source"] = source_name
            # Create run_id to link operations within the same run (per operation counter)
            df["run_id"] = df.groupby("operation").cumcount()
            data_frames.append(df)
        except Exception as e:
            print(f"Warning: Could not process file {f_path}. Error: {e}")

    if not data_frames:
        print("No data could be loaded. Exiting.")
        sys.exit(0)

    combined_df = pd.concat(data_frames, ignore_index=True)

    # Filter out 'ctus' data
    combined_df = combined_df[combined_df["source"] != "ctus"]

    # Custom source order (respected only if present)
    CUSTOM_SOURCE_ORDER = ["original", "latest", "fixed-n"]
    all_sources = combined_df["source"].unique()
    source_order = [s for s in CUSTOM_SOURCE_ORDER if s in all_sources]
    source_order.extend(sorted([s for s in all_sources if s not in source_order]))

    print(f"\nApplying custom display order: {source_order}\n")

    # Output directories
    charts_dir = os.path.join(script_dir, "..", "results", "performance_charts")
    tables_dir = os.path.join(script_dir, "..", "results", "tables")
    os.makedirs(charts_dir, exist_ok=True)
    os.makedirs(tables_dir, exist_ok=True)

    # === Visualization ===
    plot_individual_operations(combined_df, level, charts_dir, source_order)

    total_cycles_df = (
        combined_df.groupby(["source", "run_id"])["cycles"].sum().reset_index()
    )
    plot_total_comparison(total_cycles_df, level, charts_dir, source_order)
    plot_individual_operations_ieee(combined_df, level, charts_dir, source_order)
        # === Additional IEEE TOTAL (combined) boxplots ===
    plot_total_combined_ieee(combined_df, level, charts_dir, source_order)


    # === Stats tables: medians & describe ===
    section("Individual Operation Statistics")

    subsection("Median CPU Cycles per Operation")
    median_cycles = (
        combined_df.groupby(["source", "operation"])["cycles"].median().unstack()
    )
    median_cycles = median_cycles.reindex(source_order)
    print_df(median_cycles)

    subsection("Summary Statistics for CPU Cycles per Operation")
    summary_stats = combined_df.groupby(["source", "operation"])["cycles"].describe()
    summary_stats = summary_stats.reindex(source_order, level="source")
    print_df(summary_stats, floatfmt="%.2f", int_as_int=False)

    subsection("Outlier Analysis (IQR Method)")
    outlier_stats = compute_outlier_stats(combined_df)
    print_df(outlier_stats.round(2))
    outlier_stats.to_csv(os.path.join(tables_dir, f"hqc{level}_outliers.csv"))


    section("Total Cycles Statistics (keypair + encaps + decaps)")
    total_summary_stats = total_cycles_df.groupby("source")["cycles"].describe()
    total_summary_stats = total_summary_stats.reindex(source_order)
    print_df(total_summary_stats, floatfmt="%.2f", int_as_int=False)

    # === Improvement vs baseline (median) ===
    section("Performance Improvement vs Baseline (Median)")
    print(f"Baseline for comparison: '{source_order[0]}'")
    print(
        "Positive (+) values mean FASTER (fewer cycles). Negative (-) values mean SLOWER (more cycles).\n"
    )
    print_performance_improvement(median_cycles, total_summary_stats, source_order)

    # === Statistical tests: build p-value tables ===
    op_pvals, total_pvals = run_statistical_tests(combined_df, total_cycles_df, source_order)

    # Round p-values for readability
    if op_pvals is not None:
        op_show = op_pvals.copy()
        op_show["MWU_p"] = op_show["MWU_p"].round(6)
        op_show["T_p"] = op_show["T_p"].round(6)
        section("P-value Tables")
        print_df(op_show.sort_index(), title="(Operations) Mann–Whitney & Welch’s t-test p-values")

    if total_pvals is not None:
        total_show = total_pvals.copy()
        total_show["MWU_p"] = total_show["MWU_p"].round(6)
        total_show["T_p"] = total_show["T_p"].round(6)
        print_df(total_show.sort_index(), title="(Total) Mann–Whitney & Welch’s t-test p-values")

    # === Export CSVs ===
    median_cycles.to_csv(os.path.join(tables_dir, f"hqc{level}_median_cycles.csv"))
    summary_stats.to_csv(os.path.join(tables_dir, f"hqc{level}_op_describe.csv"))
    total_summary_stats.to_csv(os.path.join(tables_dir, f"hqc{level}_total_describe.csv"))
    if op_pvals is not None:
        op_pvals.to_csv(os.path.join(tables_dir, f"hqc{level}_pvalues_operations.csv"))
    if total_pvals is not None:
        total_pvals.to_csv(os.path.join(tables_dir, f"hqc{level}_pvalues_total.csv"))

    print(f"\nSaved tables to: {tables_dir}")
    print(f"Saved charts to: {charts_dir}")

    # === Optional: export a concise Markdown report ===
    if args.markdown:
        reports_dir = os.path.join(script_dir, "..", "results", "reports")
        os.makedirs(reports_dir, exist_ok=True)
        build_markdown_report(
            level,
            reports_dir,
            median_cycles,
            summary_stats,
            total_summary_stats,
            op_pvals,
            total_pvals,
        )


if __name__ == "__main__":
    main()
