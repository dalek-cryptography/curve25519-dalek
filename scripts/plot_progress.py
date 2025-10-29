#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "pandas",
#   "matplotlib",
#   "seaborn",
#   "beartype",
# ]
# ///
"""
Plot verification progress for curve25519-dalek.
Visualizes specification and proof completion status from CSV tracking data.
"""

import argparse
from pathlib import Path
from typing import Dict

import matplotlib.pyplot as plt
import pandas as pd
from beartype import beartype


@beartype
def load_data(csv_path: Path) -> pd.DataFrame:
    """Load the CSV data into a pandas DataFrame."""
    return pd.read_csv(csv_path)


@beartype
def calculate_stats(df: pd.DataFrame) -> Dict[str, int]:
    """Calculate verification statistics from the DataFrame."""
    total = len(df)

    # Verus statistics
    verus_specs = (df["has_spec_verus"].notna() & (df["has_spec_verus"] != "")).sum()
    verus_specs_full = (df["has_spec_verus"] == "yes").sum()
    verus_specs_external = (df["has_spec_verus"] == "ext").sum()
    verus_proofs = (df["has_proof_verus"] == "yes").sum()

    # Lean statistics
    lean_specs = (df["has_spec_lean"].notna() & (df["has_spec_lean"] != "")).sum()
    lean_proofs = (df["has_proof_lean"].notna() & (df["has_proof_lean"] != "")).sum()

    # Functions with no specs at all
    no_specs = (
        ((df["has_spec_verus"].isna()) | (df["has_spec_verus"] == ""))
        & ((df["has_spec_lean"].isna()) | (df["has_spec_lean"] == ""))
    ).sum()

    return {
        "total": total,
        "verus_specs": verus_specs,
        "verus_specs_full": verus_specs_full,
        "verus_specs_external": verus_specs_external,
        "verus_proofs": verus_proofs,
        "lean_specs": lean_specs,
        "lean_proofs": lean_proofs,
        "no_specs": no_specs,
    }


@beartype
def plot_overall_progress(stats: Dict[str, int], output_dir: Path):
    """Create a bar chart showing overall verification progress."""
    fig, ax = plt.subplots(figsize=(12, 6))

    total = stats["total"]

    categories = [
        "Verus\nSpecs",
        "Verus\nProofs",
        "Lean\nSpecs",
        "Lean\nProofs",
        "No\nSpecs",
    ]
    counts = [
        stats["verus_specs"],
        stats["verus_proofs"],
        stats["lean_specs"],
        stats["lean_proofs"],
        stats["no_specs"],
    ]
    percentages = [
        round(count * 100 / total, 1) if total > 0 else 0 for count in counts
    ]

    colors = ["#3498db", "#2ecc71", "#9b59b6", "#8e44ad", "#95a5a6"]
    bars = ax.bar(
        categories, counts, color=colors, alpha=0.8, edgecolor="black", linewidth=1.5
    )

    # Add percentage labels on bars
    for bar, pct, count in zip(bars, percentages, counts):
        height = bar.get_height()
        ax.text(
            bar.get_x() + bar.get_width() / 2.0,
            height + 1,
            f"{count}\n({pct}%)",
            ha="center",
            va="bottom",
            fontweight="bold",
            fontsize=11,
        )

    ax.set_ylabel("Number of Functions", fontsize=12, fontweight="bold")
    ax.set_title(
        f"Verification Progress Overview\nTotal Functions: {total}",
        fontsize=14,
        fontweight="bold",
        pad=20,
    )
    ax.set_ylim(0, max(counts) * 1.15)
    ax.grid(axis="y", alpha=0.3, linestyle="--")

    plt.tight_layout()
    output_path = output_dir / "overall_progress.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_verus_breakdown(stats: Dict[str, int], output_dir: Path):
    """Create a stacked bar chart showing Verus spec types."""
    fig, ax = plt.subplots(figsize=(10, 6))

    total = stats["total"]
    no_spec = stats["no_specs"]
    external = stats["verus_specs_external"]
    full_spec_no_proof = stats["verus_specs_full"] - stats["verus_proofs"]
    proofs = stats["verus_proofs"]

    categories = ["Verus Status"]

    # Stack from bottom to top: No Spec, External, Spec (no proof), Proof
    p1 = ax.bar(categories, [no_spec], label="No Spec", color="#e74c3c", alpha=0.8)
    p2 = ax.bar(
        categories,
        [external],
        bottom=[no_spec],
        label="External Body",
        color="#f39c12",
        alpha=0.8,
    )
    p3 = ax.bar(
        categories,
        [full_spec_no_proof],
        bottom=[no_spec + external],
        label="Spec (No Proof)",
        color="#3498db",
        alpha=0.8,
    )
    p4 = ax.bar(
        categories,
        [proofs],
        bottom=[no_spec + external + full_spec_no_proof],
        label="Verified (Proof)",
        color="#2ecc71",
        alpha=0.8,
    )

    # Add percentage labels
    def add_label(bar, value, bottom=0):
        if value > 0:
            pct = round(value * 100 / total, 1)
            ax.text(
                bar[0].get_x() + bar[0].get_width() / 2.0,
                bottom + value / 2,
                f"{value}\n({pct}%)",
                ha="center",
                va="center",
                fontweight="bold",
                fontsize=11,
                color="white" if value > total * 0.05 else "black",
            )

    add_label(p1, no_spec, 0)
    add_label(p2, external, no_spec)
    add_label(p3, full_spec_no_proof, no_spec + external)
    add_label(p4, proofs, no_spec + external + full_spec_no_proof)

    ax.set_ylabel("Number of Functions", fontsize=12, fontweight="bold")
    ax.set_title(
        f"Verus Verification Status Breakdown\nTotal Functions: {total}",
        fontsize=14,
        fontweight="bold",
        pad=20,
    )
    ax.set_ylim(0, total * 1.05)
    ax.legend(loc="upper right", fontsize=10)
    ax.set_xlim(-0.5, 0.5)

    plt.tight_layout()
    output_path = output_dir / "verus_breakdown.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_comparison_pie(stats: Dict[str, int], output_dir: Path):
    """Create pie charts comparing Verus and Lean progress."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    total = stats["total"]

    # Verus pie chart
    verus_with_proof = stats["verus_proofs"]
    verus_spec_only = stats["verus_specs"] - stats["verus_proofs"]
    verus_no_spec = total - stats["verus_specs"]

    verus_sizes = [verus_with_proof, verus_spec_only, verus_no_spec]
    verus_labels = [
        f"Verified\n{verus_with_proof} ({round(verus_with_proof * 100 / total, 1)}%)",
        f"Spec Only\n{verus_spec_only} ({round(verus_spec_only * 100 / total, 1)}%)",
        f"No Spec\n{verus_no_spec} ({round(verus_no_spec * 100 / total, 1)}%)",
    ]
    verus_colors = ["#2ecc71", "#3498db", "#e74c3c"]

    ax1.pie(
        verus_sizes,
        labels=verus_labels,
        colors=verus_colors,
        autopct="",
        startangle=90,
        explode=(0.05, 0, 0),
    )
    ax1.set_title("Verus Progress", fontsize=14, fontweight="bold", pad=20)

    # Lean pie chart
    lean_with_proof = stats["lean_proofs"]
    lean_spec_only = stats["lean_specs"] - stats["lean_proofs"]
    lean_no_spec = total - stats["lean_specs"]

    lean_sizes = [lean_with_proof, lean_spec_only, lean_no_spec]
    lean_labels = [
        f"Verified\n{lean_with_proof} ({round(lean_with_proof * 100 / total, 1)}%)",
        f"Spec Only\n{lean_spec_only} ({round(lean_spec_only * 100 / total, 1)}%)",
        f"No Spec\n{lean_no_spec} ({round(lean_no_spec * 100 / total, 1)}%)",
    ]
    lean_colors = ["#8e44ad", "#9b59b6", "#e74c3c"]

    ax2.pie(
        lean_sizes,
        labels=lean_labels,
        colors=lean_colors,
        autopct="",
        startangle=90,
        explode=(0.05, 0, 0) if lean_with_proof > 0 else (0, 0, 0),
    )
    ax2.set_title("Lean Progress", fontsize=14, fontweight="bold", pad=20)

    plt.suptitle(
        f"Verification Progress Comparison (Total: {total} functions)",
        fontsize=16,
        fontweight="bold",
        y=1.02,
    )

    plt.tight_layout()
    output_path = output_dir / "comparison_pie.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_funnel(stats: Dict[str, int], output_dir: Path):
    """Create a funnel chart showing the verification pipeline."""
    fig, ax = plt.subplots(figsize=(10, 8))

    total = stats["total"]

    # Funnel stages for Verus
    stages = [
        ("Total Functions", total),
        ("With Verus Spec", stats["verus_specs"]),
        ("With Full Spec\n(not external)", stats["verus_specs_full"]),
        ("Fully Verified", stats["verus_proofs"]),
    ]

    # Create funnel using horizontal bars
    y_positions = list(range(len(stages)))
    widths = [stage[1] for stage in stages]
    labels = [stage[0] for stage in stages]

    colors = ["#95a5a6", "#3498db", "#5dade2", "#2ecc71"]

    for i, (width, label, color) in enumerate(zip(widths, labels, colors)):
        # Calculate percentage
        pct = round(width * 100 / total, 1) if total > 0 else 0

        # Draw bar
        ax.barh(
            y_positions[i],
            width,
            height=0.6,
            color=color,
            alpha=0.8,
            edgecolor="black",
            linewidth=2,
        )

        # Add label inside bar
        ax.text(
            width / 2,
            y_positions[i],
            f"{width} ({pct}%)",
            ha="center",
            va="center",
            fontweight="bold",
            fontsize=12,
            color="white",
        )

        # Add stage label on the left
        ax.text(
            -total * 0.02,
            y_positions[i],
            label,
            ha="right",
            va="center",
            fontweight="bold",
            fontsize=11,
        )

    ax.set_xlim(-total * 0.25, total * 1.05)
    ax.set_ylim(-0.5, len(stages) - 0.5)
    ax.set_yticks([])
    ax.set_xlabel("Number of Functions", fontsize=12, fontweight="bold")
    ax.set_title(
        "Verus Verification Funnel",
        fontsize=14,
        fontweight="bold",
        pad=20,
    )
    ax.grid(axis="x", alpha=0.3, linestyle="--")
    ax.invert_yaxis()

    plt.tight_layout()
    output_path = output_dir / "verification_funnel.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_file_breakdown(df: pd.DataFrame, output_dir: Path):
    """Create a breakdown by file/module."""

    # Extract module from link
    def extract_module(link: str) -> str:
        if pd.isna(link) or not link:
            return "unknown"
        # Extract path between /blob/hash/ and file name
        import re

        match = re.search(r"/blob/[^/]+/(.+?)#", link)
        if match:
            path = match.group(1)
            # Get the parent directory
            parts = path.split("/")
            if len(parts) > 1:
                # Return last 2 parts of path (e.g., "u64/field.rs")
                return "/".join(parts[-2:]) if len(parts) >= 2 else parts[-1]
            return parts[-1]
        return "unknown"

    df["module"] = df["link"].apply(extract_module)

    # Count by module
    module_stats = []
    for module in df["module"].unique():
        module_df = df[df["module"] == module]
        total = len(module_df)
        verus_specs = (
            module_df["has_spec_verus"].notna() & (module_df["has_spec_verus"] != "")
        ).sum()
        verus_proofs = (module_df["has_proof_verus"] == "yes").sum()

        module_stats.append(
            {
                "module": module,
                "total": total,
                "verus_specs": verus_specs,
                "verus_proofs": verus_proofs,
                "spec_pct": round(verus_specs * 100 / total, 1) if total > 0 else 0,
                "proof_pct": round(verus_proofs * 100 / total, 1) if total > 0 else 0,
            }
        )

    # Sort by total functions
    module_stats.sort(key=lambda x: x["total"], reverse=True)

    # Take top 15 modules
    top_modules = module_stats[:15]

    # Create grouped bar chart
    fig, ax = plt.subplots(figsize=(14, 8))

    x = range(len(top_modules))
    width = 0.35

    specs = [m["verus_specs"] for m in top_modules]
    proofs = [m["verus_proofs"] for m in top_modules]
    labels = [m["module"] for m in top_modules]

    ax.bar(
        [i - width / 2 for i in x],
        specs,
        width,
        label="Specs",
        color="#3498db",
        alpha=0.8,
    )
    ax.bar(
        [i + width / 2 for i in x],
        proofs,
        width,
        label="Proofs",
        color="#2ecc71",
        alpha=0.8,
    )

    ax.set_xlabel("Module/File", fontsize=12, fontweight="bold")
    ax.set_ylabel("Number of Functions", fontsize=12, fontweight="bold")
    ax.set_title(
        "Top 15 Modules by Function Count - Verus Progress",
        fontsize=14,
        fontweight="bold",
        pad=20,
    )
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=9)
    ax.legend()
    ax.grid(axis="y", alpha=0.3, linestyle="--")

    plt.tight_layout()
    output_path = output_dir / "module_breakdown.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def print_summary(stats: Dict[str, int]):
    """Print a text summary of the statistics."""
    total = stats["total"]

    print("\n" + "=" * 60)
    print("VERIFICATION PROGRESS SUMMARY")
    print("=" * 60)
    print(f"\nTotal Functions: {total}")
    print(f"\n{'VERUS':^60}")
    print("-" * 60)
    print(
        f"  Total with specs:      {stats['verus_specs']:4d} ({round(stats['verus_specs'] * 100 / total, 1):5.1f}%)"
    )
    print(
        f"    - Full specs:        {stats['verus_specs_full']:4d} ({round(stats['verus_specs_full'] * 100 / total, 1):5.1f}%)"
    )
    print(
        f"    - External body:     {stats['verus_specs_external']:4d} ({round(stats['verus_specs_external'] * 100 / total, 1):5.1f}%)"
    )
    print(
        f"  Fully verified:        {stats['verus_proofs']:4d} ({round(stats['verus_proofs'] * 100 / total, 1):5.1f}%)"
    )

    print(f"\n{'LEAN':^60}")
    print("-" * 60)
    print(
        f"  Total with specs:      {stats['lean_specs']:4d} ({round(stats['lean_specs'] * 100 / total, 1):5.1f}%)"
    )
    print(
        f"  Fully verified:        {stats['lean_proofs']:4d} ({round(stats['lean_proofs'] * 100 / total, 1):5.1f}%)"
    )

    print(f"\n{'OVERALL':^60}")
    print("-" * 60)
    print(
        f"  No specs (any system): {stats['no_specs']:4d} ({round(stats['no_specs'] * 100 / total, 1):5.1f}%)"
    )
    print("=" * 60 + "\n")


@beartype
def main():
    parser = argparse.ArgumentParser(
        description="Plot verification progress for curve25519-dalek"
    )
    parser.add_argument(
        "--csv",
        type=str,
        default="curve25519_functions.csv",
        help="CSV file name (default: curve25519_functions.csv)",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default="outputs",
        help="Output directory for plots (default: outputs)",
    )
    args = parser.parse_args()

    # Set up paths
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent
    outputs_dir = repo_root / "outputs"
    csv_path = outputs_dir / args.csv
    output_dir = repo_root / args.output_dir

    if not csv_path.exists():
        print(f"Error: CSV file not found at {csv_path}")
        return

    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Loading data from: {csv_path}")
    df = load_data(csv_path)

    print("Calculating statistics...")
    stats = calculate_stats(df)

    # Print summary
    print_summary(stats)

    # Generate plots
    print(f"\nGenerating plots to: {output_dir}")
    print("-" * 60)

    plot_overall_progress(stats, output_dir)
    plot_verus_breakdown(stats, output_dir)
    plot_comparison_pie(stats, output_dir)
    plot_funnel(stats, output_dir)
    plot_file_breakdown(df, output_dir)

    print("-" * 60)
    print(f"\nAll plots saved to: {output_dir}")
    print("\nGenerated files:")
    print("  - overall_progress.png")
    print("  - verus_breakdown.png")
    print("  - comparison_pie.png")
    print("  - verification_funnel.png")
    print("  - module_breakdown.png")


if __name__ == "__main__":
    main()
