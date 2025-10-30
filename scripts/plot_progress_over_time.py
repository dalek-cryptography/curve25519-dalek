#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "pandas",
#   "matplotlib",
#   "seaborn",
#   "beartype",
#   "gitpython",
# ]
# ///
"""
Plot verification progress over time by analyzing git history.
Tracks how specs and proofs have evolved across commits on main branch.
"""

import argparse
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import pandas as pd
from beartype import beartype
from git import Repo


@beartype
def get_commit_history(
    repo_path: Path,
    branch: str = "main",
    since_date: str | None = None,
    max_commits: int = 50,
) -> List[Tuple[str, datetime, str]]:
    """
    Get git commit history with dates.

    Returns:
        List of (commit_hash, commit_date, commit_message) tuples
    """
    repo = Repo(repo_path)

    # Get commits from specified branch
    try:
        commits = list(repo.iter_commits(branch, max_count=max_commits))
    except Exception:
        print(f"Warning: Could not access branch '{branch}', trying current branch")
        commits = list(repo.iter_commits(max_count=max_commits))

    commit_data = []
    for commit in commits:
        commit_date = datetime.fromtimestamp(commit.committed_date)

        # Filter by date if specified
        if since_date:
            since = datetime.strptime(since_date, "%Y-%m-%d")
            if commit_date < since:
                break

        commit_data.append(
            (
                commit.hexsha,
                commit_date,
                commit.message.strip().split("\n")[0][:60],  # First line, truncated
            )
        )

    return commit_data


@beartype
def analyze_csv_at_commit(
    repo_path: Path, commit_hash: str, csv_relative_path: str
) -> Dict[str, int] | None:
    """
    Analyze the CSV file at a specific commit without checking out.

    Returns:
        Dictionary with stats or None if CSV doesn't exist at that commit
    """
    repo = Repo(repo_path)

    try:
        # Get the file content at this commit
        commit = repo.commit(commit_hash)

        # Try to get the CSV file from this commit
        try:
            csv_blob = commit.tree / csv_relative_path
            csv_content = csv_blob.data_stream.read().decode("utf-8")
        except KeyError:
            # CSV doesn't exist at this commit
            return None

        # Parse CSV content
        import io
        import csv

        lines = csv_content.strip().split("\n")
        if len(lines) < 2:  # No data rows
            return None

        reader = csv.DictReader(io.StringIO(csv_content))
        rows = list(reader)

        if not rows:
            return None

        total = len(rows)

        # Check if columns exist (CSV structure might have changed over time)
        has_verus_spec_col = "has_spec_verus" in rows[0]
        has_verus_proof_col = "has_proof_verus" in rows[0]
        has_lean_spec_col = "has_spec_lean" in rows[0]
        has_lean_proof_col = "has_proof_lean" in rows[0]

        # Count Verus stats
        verus_specs = 0
        verus_specs_full = 0
        verus_specs_external = 0
        verus_proofs = 0

        if has_verus_spec_col:
            for row in rows:
                spec_val = row.get("has_spec_verus", "").strip()
                if spec_val:
                    verus_specs += 1
                    if spec_val == "yes":
                        verus_specs_full += 1
                    elif spec_val == "ext":
                        verus_specs_external += 1

        if has_verus_proof_col:
            verus_proofs = sum(
                1 for row in rows if row.get("has_proof_verus", "").strip() == "yes"
            )

        # Count Lean stats
        lean_specs = 0
        lean_proofs = 0

        if has_lean_spec_col:
            lean_specs = sum(1 for row in rows if row.get("has_spec_lean", "").strip())

        if has_lean_proof_col:
            lean_proofs = sum(
                1 for row in rows if row.get("has_proof_lean", "").strip()
            )

        return {
            "total": total,
            "verus_specs": verus_specs,
            "verus_specs_full": verus_specs_full,
            "verus_specs_external": verus_specs_external,
            "verus_proofs": verus_proofs,
            "lean_specs": lean_specs,
            "lean_proofs": lean_proofs,
        }

    except Exception as e:
        print(f"  Error analyzing commit {commit_hash[:8]}: {e}")
        return None


@beartype
def collect_historical_data(
    repo_path: Path,
    csv_relative_path: str,
    branch: str = "main",
    since_date: str | None = None,
    max_commits: int = 50,
    sample_interval: int = 1,
) -> pd.DataFrame:
    """
    Collect verification statistics across git history.

    Args:
        sample_interval: Only analyze every Nth commit (1 = all commits)
    """
    print(f"Analyzing git history on branch '{branch}'...")
    print(f"CSV path: {csv_relative_path}")
    print()

    commits = get_commit_history(repo_path, branch, since_date, max_commits)
    print(f"Found {len(commits)} commits to analyze")

    if sample_interval > 1:
        commits = commits[::sample_interval]
        print(f"Sampling every {sample_interval} commits: {len(commits)} commits")

    print()

    historical_data = []

    for i, (commit_hash, commit_date, commit_msg) in enumerate(commits, 1):
        print(
            f"[{i}/{len(commits)}] {commit_date.strftime('%Y-%m-%d')} {commit_hash[:8]} - {commit_msg}"
        )

        stats = analyze_csv_at_commit(repo_path, commit_hash, csv_relative_path)

        if stats is None:
            print("  -> CSV not found or invalid at this commit, skipping")
            continue

        print(
            f"  -> Total: {stats['total']}, Verus specs: {stats['verus_specs']}, Verus proofs: {stats['verus_proofs']}"
        )

        historical_data.append(
            {
                "commit": commit_hash[:8],
                "date": commit_date,
                "message": commit_msg,
                **stats,
            }
        )

    print()

    if not historical_data:
        raise ValueError("No valid data found in commit history")

    df = pd.DataFrame(historical_data)
    df = df.sort_values("date")  # Sort chronologically

    return df


@beartype
def plot_progress_over_time(df: pd.DataFrame, output_dir: Path):
    """Create a line chart showing verification progress over time."""
    fig, ax = plt.subplots(figsize=(14, 8))

    # Convert to percentages
    df["verus_specs_pct"] = (df["verus_specs"] / df["total"]) * 100
    df["verus_proofs_pct"] = (df["verus_proofs"] / df["total"]) * 100
    df["lean_specs_pct"] = (df["lean_specs"] / df["total"]) * 100
    df["lean_proofs_pct"] = (df["lean_proofs"] / df["total"]) * 100

    # Plot lines
    ax.plot(
        df["date"],
        df["verus_specs_pct"],
        marker="o",
        linewidth=2.5,
        markersize=6,
        label="Verus Specs",
        color="#3498db",
        alpha=0.9,
    )
    ax.plot(
        df["date"],
        df["verus_proofs_pct"],
        marker="s",
        linewidth=2.5,
        markersize=6,
        label="Verus Proofs",
        color="#2ecc71",
        alpha=0.9,
    )

    # Only plot Lean if there's data
    if df["lean_specs_pct"].max() > 0:
        ax.plot(
            df["date"],
            df["lean_specs_pct"],
            marker="^",
            linewidth=2.5,
            markersize=6,
            label="Lean Specs",
            color="#9b59b6",
            alpha=0.9,
        )

    if df["lean_proofs_pct"].max() > 0:
        ax.plot(
            df["date"],
            df["lean_proofs_pct"],
            marker="d",
            linewidth=2.5,
            markersize=6,
            label="Lean Proofs",
            color="#8e44ad",
            alpha=0.9,
        )

    # Fill areas under curves
    ax.fill_between(
        df["date"],
        0,
        df["verus_proofs_pct"],
        alpha=0.2,
        color="#2ecc71",
    )

    ax.set_xlabel("Date", fontsize=12, fontweight="bold")
    ax.set_ylabel("Percentage of Functions (%)", fontsize=12, fontweight="bold")
    ax.set_title(
        "Verification Progress Over Time",
        fontsize=16,
        fontweight="bold",
        pad=20,
    )
    ax.set_ylim(0, max(100, df["verus_specs_pct"].max() * 1.1))
    # Set x-axis limits to actual data range
    ax.set_xlim(df["date"].min(), df["date"].max())
    ax.grid(True, alpha=0.3, linestyle="--")
    ax.legend(loc="upper left", fontsize=11, framealpha=0.9)

    # Rotate date labels
    plt.xticks(rotation=45, ha="right")

    # Add annotations for last point
    last_row = df.iloc[-1]

    ax.annotate(
        f"{last_row['verus_proofs_pct']:.1f}%",
        xy=(last_row["date"], last_row["verus_proofs_pct"]),
        xytext=(10, 10),
        textcoords="offset points",
        fontweight="bold",
        fontsize=10,
        bbox=dict(boxstyle="round,pad=0.3", facecolor="#2ecc71", alpha=0.7),
        color="white",
    )

    plt.tight_layout()
    output_path = output_dir / "progress_over_time.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_absolute_counts(df: pd.DataFrame, output_dir: Path):
    """Create a stacked area chart showing absolute counts over time."""
    fig, ax = plt.subplots(figsize=(14, 8))

    # Create stacked areas for Verus
    ax.fill_between(
        df["date"],
        0,
        df["verus_proofs"],
        label="Verified (Proofs)",
        color="#2ecc71",
        alpha=0.8,
    )

    ax.fill_between(
        df["date"],
        df["verus_proofs"],
        df["verus_specs"],
        label="Specs (No Proof)",
        color="#3498db",
        alpha=0.5,
    )

    # Plot total as a line
    ax.plot(
        df["date"],
        df["total"],
        linewidth=2.5,
        label="Total Functions",
        color="#34495e",
        linestyle="--",
        marker="o",
        markersize=5,
    )

    ax.set_xlabel("Date", fontsize=12, fontweight="bold")
    ax.set_ylabel("Number of Functions", fontsize=12, fontweight="bold")
    ax.set_title(
        "Absolute Function Counts Over Time",
        fontsize=16,
        fontweight="bold",
        pad=20,
    )

    # Set y-axis ticks every 25 functions
    import numpy as np

    max_val = int(df["total"].max())
    y_ticks = np.arange(0, max_val + 50, 25)
    ax.set_yticks(y_ticks)

    # Add y-axis labels on the right side as well
    ax.tick_params(axis="y", which="both", labelleft=True, labelright=True, right=True)

    ax.grid(True, alpha=0.8, linestyle="--", axis="y")
    ax.legend(loc="upper left", fontsize=11, framealpha=0.9)

    # Set x-axis limits to actual data range
    ax.set_xlim(df["date"].min(), df["date"].max())

    # Format x-axis dates as "Oct 11", "Oct 13", etc.
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    plt.xticks(rotation=45, ha="right")
    plt.tight_layout()

    output_path = output_dir / "absolute_counts_over_time.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def plot_velocity(df: pd.DataFrame, output_dir: Path):
    """Plot the rate of change (velocity) of verification progress."""
    if len(df) < 2:
        print("Not enough data points to calculate velocity")
        return

    fig, ax = plt.subplots(figsize=(14, 8))

    # Calculate differences between consecutive commits
    df = df.copy()
    df["specs_delta"] = df["verus_specs"].diff()
    df["proofs_delta"] = df["verus_proofs"].diff()
    df["days_delta"] = df["date"].diff().dt.total_seconds() / (24 * 3600)

    # Remove first row (NaN values)
    df_velocity = df.iloc[1:].copy()

    # Bar chart showing deltas
    x = range(len(df_velocity))
    width = 0.35

    ax.bar(
        [i - width / 2 for i in x],
        df_velocity["specs_delta"],
        width,
        label="Specs Added",
        color="#3498db",
        alpha=0.8,
    )

    ax.bar(
        [i + width / 2 for i in x],
        df_velocity["proofs_delta"],
        width,
        label="Proofs Added",
        color="#2ecc71",
        alpha=0.8,
    )

    # Add zero line
    ax.axhline(y=0, color="black", linestyle="-", linewidth=0.8, alpha=0.5)

    ax.set_xlabel("Commit", fontsize=12, fontweight="bold")
    ax.set_ylabel("Functions Added", fontsize=12, fontweight="bold")
    ax.set_title(
        "Verification Velocity (Changes Per Commit)",
        fontsize=16,
        fontweight="bold",
        pad=20,
    )
    ax.set_xticks(x)
    ax.set_xticklabels(df_velocity["commit"], rotation=45, ha="right", fontsize=9)
    ax.legend(fontsize=11)
    ax.grid(axis="y", alpha=0.3, linestyle="--")

    plt.tight_layout()
    output_path = output_dir / "verification_velocity.png"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    print(f"Saved: {output_path}")
    plt.close()


@beartype
def print_summary(df: pd.DataFrame) -> dict:
    """Print summary statistics and return metadata."""
    print("\n" + "=" * 70)
    print("HISTORICAL PROGRESS SUMMARY")
    print("=" * 70)

    first = df.iloc[0]
    last = df.iloc[-1]

    total_days = (last["date"] - first["date"]).days

    print(
        f"\nTime Period: {first['date'].strftime('%Y-%m-%d')} to {last['date'].strftime('%Y-%m-%d')}"
    )
    print(f"Duration: {total_days} days ({len(df)} commits analyzed)")

    print(f"\n{'VERUS - First Commit':^70}")
    print("-" * 70)
    print(f"  Total functions:  {first['total']:4d}")
    print(
        f"  With specs:       {first['verus_specs']:4d} ({first['verus_specs'] / first['total'] * 100:5.1f}%)"
    )
    print(
        f"  With proofs:      {first['verus_proofs']:4d} ({first['verus_proofs'] / first['total'] * 100:5.1f}%)"
    )

    print(f"\n{'VERUS - Latest Commit':^70}")
    print("-" * 70)
    print(f"  Total functions:  {last['total']:4d}")
    print(
        f"  With specs:       {last['verus_specs']:4d} ({last['verus_specs'] / last['total'] * 100:5.1f}%)"
    )
    print(
        f"  With proofs:      {last['verus_proofs']:4d} ({last['verus_proofs'] / last['total'] * 100:5.1f}%)"
    )

    print(f"\n{'PROGRESS MADE':^70}")
    print("-" * 70)
    specs_added = last["verus_specs"] - first["verus_specs"]
    proofs_added = last["verus_proofs"] - first["verus_proofs"]
    print(f"  Specs added:      {specs_added:+4d}")
    print(f"  Proofs added:     {proofs_added:+4d}")

    if total_days > 0:
        specs_per_day = specs_added / total_days
        proofs_per_day = proofs_added / total_days
        print(f"\n{'VELOCITY':^70}")
        print("-" * 70)
        print(f"  Specs/day:        {specs_per_day:+.2f}")
        print(f"  Proofs/day:       {proofs_per_day:+.2f}")

    print("=" * 70 + "\n")

    # Return metadata for JSON export
    return {
        "first_date": first["date"].strftime("%Y-%m-%d"),
        "last_date": last["date"].strftime("%Y-%m-%d"),
        "total_days": total_days,
        "commits_analyzed": len(df),
    }


@beartype
def main():
    parser = argparse.ArgumentParser(
        description="Plot verification progress over time from git history"
    )
    parser.add_argument(
        "--branch",
        type=str,
        default="main",
        help="Git branch to analyze (default: main)",
    )
    parser.add_argument(
        "--csv-path",
        type=str,
        default="outputs/curve25519_functions.csv",
        help="Relative path to CSV file from repo root (default: outputs/curve25519_functions.csv)",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default="outputs",
        help="Output directory for plots (default: outputs)",
    )
    parser.add_argument(
        "--since",
        type=str,
        help="Only analyze commits since this date (YYYY-MM-DD)",
    )
    parser.add_argument(
        "--max-commits",
        type=int,
        default=50,
        help="Maximum number of commits to analyze (default: 50)",
    )
    parser.add_argument(
        "--sample",
        type=int,
        default=1,
        help="Sample every Nth commit (default: 1 = all commits)",
    )
    args = parser.parse_args()

    # Set up paths
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent
    output_dir = repo_root / args.output_dir

    output_dir.mkdir(parents=True, exist_ok=True)

    # Collect historical data
    df = collect_historical_data(
        repo_path=repo_root,
        csv_relative_path=args.csv_path,
        branch=args.branch,
        since_date=args.since,
        max_commits=args.max_commits,
        sample_interval=args.sample,
    )

    # Print summary and get metadata
    metadata = print_summary(df)

    # Write metadata to JSON for website
    import json

    metadata_path = output_dir / "metadata.json"
    with open(metadata_path, "w") as f:
        json.dump(metadata, f, indent=2)
    print(f"\nMetadata saved to: {metadata_path}")

    # Generate plots
    print(f"Generating temporal plots to: {output_dir}")
    print("-" * 70)

    plot_progress_over_time(df, output_dir)
    plot_absolute_counts(df, output_dir)
    plot_velocity(df, output_dir)

    print("-" * 70)
    print(f"\nAll plots saved to: {output_dir}")
    print("\nGenerated files:")
    print("  - progress_over_time.png")
    print("  - absolute_counts_over_time.png")
    print("  - verification_velocity.png")


if __name__ == "__main__":
    main()
