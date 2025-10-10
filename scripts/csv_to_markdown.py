#!/usr/bin/env python3
"""Convert curve25519_functions.csv to markdown format with links and checkboxes."""

import csv
from pathlib import Path


def main():
    # Get repo root (scripts/ -> repo_root/)
    repo_root = Path(__file__).parent.parent
    csv_path = repo_root / "outputs" / "curve25519_functions.csv"
    md_path = repo_root / "outputs" / "curve25519_functions.md"

    with open(csv_path, "r", encoding="utf-8") as csvfile:
        reader = csv.DictReader(csvfile)

        # Prepare markdown content
        lines = []
        lines.append("# Curve25519 Functions\n")
        lines.append(
            "| Function | Has Spec (Verus) | Has Proof (Verus) | Has Spec (Lean) | Has Proof (Lean) |"
        )
        lines.append(
            "|----------|:------------------:|:-------------------:|:----------------:|:-----------------:|"
        )

        for row in reader:
            function_name = row["function_name"].strip()
            link = row["link"].strip()
            has_spec_verus = row["has_spec_verus"].strip()
            has_proof_verus = row["has_proof_verus"].strip()
            has_spec_lean = row["has_spec_lean"].strip()
            has_proof_lean = row["has_proof_lean"].strip()

            # Create function link or plain text if no link
            if link:
                function_cell = f"[{function_name}]({link})"
            else:
                function_cell = function_name

            # Convert has_* fields to checkboxes
            def to_checkbox(value):
                # Debug: print the value to see what we're getting
                #print(f"Debug: checkbox value = '{value}', type = {type(value)}")
                if value and value.lower() in ["true", "yes", "x", "1"]:
                    return ":heavy_check_mark:"
                else:
                    return ""

            spec_verus_cb = to_checkbox(has_spec_verus)
            proof_verus_cb = to_checkbox(has_proof_verus)
            spec_lean_cb = to_checkbox(has_spec_lean)
            proof_lean_cb = to_checkbox(has_proof_lean)

            lines.append(
                f"| {function_cell} | {spec_verus_cb} | {proof_verus_cb} | {spec_lean_cb} | {proof_lean_cb} |"
            )

        # Write to markdown file
        with open(md_path, "w", encoding="utf-8") as mdfile:
            mdfile.write("\n".join(lines) + "\n")

        print(f"✓ Markdown file created: {md_path}")
        print(f"  Total functions: {len(lines) - 3}")  # Subtract header rows


if __name__ == "__main__":
    main()
