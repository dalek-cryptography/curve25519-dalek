#!/usr/bin/env python3
"""Generate a visual preview/snapshot of the CSV file as an image."""

import json
import pandas as pd
import matplotlib.pyplot as plt
from pathlib import Path


def create_csv_preview() -> None:
    """Create a table image showing a preview of the CSV data."""
    # Read CSV
    csv_path = Path(__file__).parent.parent / "outputs" / "curve25519_functions.csv"
    df = pd.read_csv(csv_path)

    # Sample functions to show - mix of different statuses
    verified = df[df["has_proof"] == "yes"].head(8)
    external = df[df["has_spec"] == "ext"].head(6)
    with_specs = df[(df["has_spec"] == "yes") & (df["has_proof"] != "yes")].head(6)

    # Combine samples
    sample = pd.concat([verified, external, with_specs]).head(25)

    # Prepare display data
    display_data = []
    for _, row in sample.iterrows():
        func_name = row["function"]
        # Truncate long function names
        if len(func_name) > 40:
            func_name = func_name[:37] + "..."

        # Get module (now a column in the CSV)
        module = row["module"]
        # Shorten module for display - show last 2 parts
        if "::" in module:
            parts = module.split("::")
            module = "::".join(parts[-2:])

        # Determine status
        if row["has_proof"] == "yes":
            status = "✓ Verified"
        elif row["has_spec"] == "ext":
            status = "⊕ External"
        elif row["has_spec"] == "yes":
            status = "○ Spec Only"
        else:
            status = "· No Spec"

        display_data.append([func_name, module, status])

    # Create figure
    fig, ax = plt.subplots(figsize=(14, 10))
    ax.axis("tight")
    ax.axis("off")

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

    # Load counts from specs_data.json for accurate totals (with CSV fallback)
    specs_path = Path(__file__).parent.parent / "docs" / "specs_data.json"
    specified = verified_count = external_count = axiom_count = None
    if specs_path.exists():
        try:
            with open(specs_path) as f:
                raw = json.load(f)
            data = raw.get("data", raw)
            vf = data.get("verified_functions", [])
            sf = data.get("spec_functions", [])
            specified = len([f for f in vf if f.get("category") == "tracked"])
            verified_count = len(
                [f for f in vf if f.get("category") == "tracked" and f.get("has_proof")]
            )
            external_count = len([f for f in vf if f.get("category") == "external"])
            axiom_count = len([f for f in sf if f.get("category") == "axiom"])
        except (OSError, json.JSONDecodeError, TypeError):
            pass
    if specified is None:
        specified = int(((df["has_spec"] == "yes") | (df["has_spec"] == "ext")).sum())
        verified_count = int((df["has_proof"] == "yes").sum())
        external_count = int((df["has_spec"] == "ext").sum())
        axiom_count = 0

    summary_text = (
        f"Specified: {specified}  |  "
        f"Verified: {verified_count}  |  "
        f"External: {external_count}  |  "
        f"Axioms: {axiom_count}"
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
