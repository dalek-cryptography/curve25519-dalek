#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""
Update the website by regenerating all plots and copying them to docs.
This script should be run before deploying to GitHub Pages.
"""

import subprocess
import shutil
from pathlib import Path


def main():
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent
    outputs_dir = repo_root / "outputs"
    docs_dir = repo_root / "docs"
    docs_outputs = docs_dir / "outputs"

    print("=" * 70)
    print("UPDATING WEBSITE")
    print("=" * 70)

    # Step 1: Run the analysis script to update CSV
    print("\n1. Analyzing Verus specs and proofs...")
    result = subprocess.run(
        [str(script_dir / "analyze_verus_specs_proofs.py")],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"Error: {result.stderr}")
        return 1
    print("✓ Analysis complete")

    # Step 2: Generate static snapshot plots
    print("\n2. Generating snapshot plots...")
    result = subprocess.run(
        [str(script_dir / "plot_progress.py")],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"Error: {result.stderr}")
        return 1
    print("✓ Snapshot plots generated")

    # Step 3: Generate temporal plots
    print("\n3. Generating temporal plots...")
    result = subprocess.run(
        [
            str(script_dir / "plot_progress_over_time.py"),
            "--max-commits",
            "200",
            "--sample",
            "3",
        ],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"Error: {result.stderr}")
        return 1
    print("✓ Temporal plots generated")

    # Step 4: Copy plots to docs directory
    print("\n4. Copying plots to docs directory...")
    docs_outputs.mkdir(parents=True, exist_ok=True)

    plot_files = [
        "overall_progress.png",
        "verus_breakdown.png",
        "comparison_pie.png",
        "verification_funnel.png",
        "module_breakdown.png",
        "progress_over_time.png",
        "absolute_counts_over_time.png",
        "verification_velocity.png",
    ]

    for plot_file in plot_files:
        src = outputs_dir / plot_file
        dst = docs_outputs / plot_file
        if src.exists():
            shutil.copy2(src, dst)
            print(f"  ✓ Copied {plot_file}")
        else:
            print(f"  ✗ Missing {plot_file}")

    print("\n" + "=" * 70)
    print("WEBSITE UPDATE COMPLETE")
    print("=" * 70)
    print(f"\nWebsite files are in: {docs_dir}")
    print("\nTo view locally:")
    print(f"  cd {docs_dir}")
    print("  python -m http.server 8000")
    print("  Open http://localhost:8000 in your browser")
    print("\nTo deploy to GitHub Pages:")
    print("  1. Commit the changes")
    print("  2. Enable GitHub Pages in repo settings (use 'docs' folder)")
    print("  3. Push to GitHub")
    print()


if __name__ == "__main__":
    exit(main() or 0)
