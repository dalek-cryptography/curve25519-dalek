#!/usr/bin/env python3
"""Generate a visual preview/snapshot of the CSV file as an image."""

import pandas as pd
import matplotlib.pyplot as plt
from pathlib import Path


def create_csv_preview() -> None:
    """Create a table image showing a preview of the CSV data."""
    # Read CSV
    csv_path = Path(__file__).parent.parent / "outputs" / "curve25519_functions.csv"
    df = pd.read_csv(csv_path)

    # Sample functions to show - mix of different statuses
    verified = df[df["has_proof_verus"] == "yes"].head(8)
    with_specs = df[
        (df["has_spec_verus"] == "yes") & (df["has_proof_verus"] != "yes")
    ].head(8)
    no_specs = df[
        (df["has_spec_verus"] != "yes") & (df["has_proof_verus"] != "yes")
    ].head(8)

    # Combine samples
    sample = pd.concat([verified, with_specs, no_specs]).head(25)

    # Prepare display data
    display_data = []
    for _, row in sample.iterrows():
        func_name = row["function_name"]
        # Truncate long function names
        if len(func_name) > 40:
            func_name = func_name[:37] + "..."

        # Extract module from link
        link = row["link"]
        module = "unknown"
        if pd.notna(link) and ".rs#" in link:
            # Extract filename.rs from GitHub URL
            # Format: .../path/to/file.rs#L123
            match = link.split(".rs#")[0]
            if "/" in match:
                module = match.split("/")[-1] + ".rs"

        # Determine status
        if row["has_proof_verus"] == "yes":
            status = "✓ Verified"
        elif row["has_spec_verus"] == "ext":
            status = "⊕ External"
        elif row["has_spec_verus"] == "yes":
            status = "○ Spec Only"
        else:
            status = "· No Spec"

        display_data.append([func_name, module, status])

    # Create figure
    fig, ax = plt.subplots(figsize=(14, 10))
    ax.axis("tight")
    ax.axis("off")

    # Add title and subtitle
    fig.text(
        0.5,
        0.96,
        "Function Verification Status Preview",
        ha="center",
        fontsize=16,
        fontweight="bold",
    )
    fig.text(
        0.5,
        0.93,
        f"Sample of 25 functions from 257 total • Full data: outputs/curve25519_functions.csv",
        ha="center",
        fontsize=10,
        color="#666",
    )

    # Create table
    table = ax.table(
        cellText=display_data,
        colLabels=["Function Name", "Module", "Status"],
        cellLoc="left",
        loc="center",
        colWidths=[0.5, 0.25, 0.25],
    )

    # Style the table
    table.auto_set_font_size(False)
    table.set_fontsize(8)
    table.scale(1, 2)

    # Style header
    for i in range(3):
        cell = table[(0, i)]
        cell.set_facecolor("#2c3e50")
        cell.set_text_props(weight="bold", color="white", fontsize=9)

    # Style cells with alternating colors
    for i in range(1, len(display_data) + 1):
        for j in range(3):
            cell = table[(i, j)]
            if i % 2 == 0:
                cell.set_facecolor("#f8f9fa")
            else:
                cell.set_facecolor("white")

            # Color code status column
            if j == 2:  # Status column
                text = cell.get_text().get_text()
                if "Verified" in text:
                    cell.set_text_props(color="#065f46", weight="bold")
                elif "External" in text:
                    cell.set_text_props(color="#92400e", weight="bold")
                elif "Spec Only" in text:
                    cell.set_text_props(color="#1e40af", weight="bold")
                else:
                    cell.set_text_props(color="#6b7280")

    # Add summary stats at bottom
    total = len(df)
    verified_count = len(df[df["has_proof_verus"] == "yes"])
    spec_count = len(df[df["has_spec_verus"] == "yes"])

    summary_text = (
        f"Total Functions: {total}  |  "
        f"Verified: {verified_count}  |  "
        f"With Specs: {spec_count}  |  "
        f"Completion Rate: {verified_count/spec_count*100:.1f}%"
    )

    fig.text(
        0.5,
        0.04,
        summary_text,
        ha="center",
        fontsize=10,
        bbox={"boxstyle": "round", "facecolor": "#e3f2fd", "alpha": 0.8},
    )

    # Save
    output_path = Path(__file__).parent.parent / "outputs" / "csv_preview.png"
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches="tight", facecolor="white")
    plt.close()

    print(f"✓ CSV preview saved to {output_path}")


if __name__ == "__main__":
    create_csv_preview()

