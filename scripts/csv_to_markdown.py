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

        # Validate expected columns (probe-verus tracked-csv output)
        expected_cols = {"function", "module", "link", "has_spec", "has_proof"}
        if not reader.fieldnames:
            raise SystemExit(f"Error: {csv_path} is empty or has no header row")
        actual_cols = set(reader.fieldnames)
        missing = expected_cols - actual_cols
        if missing:
            raise SystemExit(
                f"Error: {csv_path} is missing columns: {sorted(missing)}\n"
                f"  Expected: {sorted(expected_cols)}\n"
                f"  Got:      {sorted(actual_cols)}"
            )

        # Prepare markdown content
        lines = []
        lines.append("# Curve25519 Functions\n")
        lines.append("| Function | Module | Has Spec (Verus) | Has Proof (Verus) |")
        lines.append("|----------|--------|:----------------:|:-----------------:|")

        for row in reader:
            function_name = row["function"].strip()
            module = row["module"].strip()
            link = row["link"].strip()
            has_spec = row["has_spec"].strip()
            has_proof = row["has_proof"].strip()

            # Create function link or plain text if no link
            if link:
                function_cell = f"[{function_name}]({link})"
            else:
                function_cell = function_name

            # Convert has_* fields to checkboxes or markers
            def to_checkbox(value):
                if value and value.lower() in ["true", "yes", "x", "1"]:
                    return ":heavy_check_mark:"
                elif value and value.lower() == "ext":
                    return ":x:"  # X mark for external_body
                else:
                    return ""

            spec_cb = to_checkbox(has_spec)
            proof_cb = to_checkbox(has_proof)

            lines.append(f"| {function_cell} | {module} | {spec_cb} | {proof_cb} |")

        # Write to markdown file
        with open(md_path, "w", encoding="utf-8") as mdfile:
            mdfile.write("\n".join(lines) + "\n")

        print(f"✓ Markdown file created: {md_path}")
        print(f"  Total functions: {len(lines) - 3}")  # Subtract header rows


if __name__ == "__main__":
    main()
