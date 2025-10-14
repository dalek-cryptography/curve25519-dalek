#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "beartype",
# ]
# ///
"""
Analyze Verus specs and proofs in curve25519-dalek source code.
Updates the CSV to mark which functions have Verus specs and/or proofs.
"""

import argparse
import csv
import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from beartype import beartype



@beartype
def parse_function_in_file(
    file_path: Path, function_name: str
) -> Tuple[bool, bool]:
    """
    Parse a Rust file to find a function and check if it has Verus specs and proofs.

    Returns:
        Tuple[bool, bool]: (has_spec, has_proof) or None if function not found
        - has_spec: True if function has requires or ensures clauses
        - has_proof: True if has_spec and no assume in body
    """
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    # Pattern to match function definitions
    # Matches: fn function_name, pub fn function_name, pub const fn function_name, etc.
    # This regex looks for function definitions
    fn_pattern = (
        r"(?:pub\s+)?(?:const\s+)?fn\s+" + re.escape(function_name) + r"\s*[<\(]"
    )

    # Find all occurrences of the function
    matches = list(re.finditer(fn_pattern, content))

    assert matches

    # For each match, check if it has specs
    for match in matches:
        fn_start = match.start()

        # Find the function body by looking for the opening brace
        fn_def_start = fn_start
        brace_pos = content.find("{", fn_def_start)

        if brace_pos == -1:
            # Might be a trait definition without body
            continue

        # Extract the signature (between fn keyword and opening brace)
        signature = content[fn_start:brace_pos]

        # Check for requires or ensures in the signature
        has_requires = "requires" in signature
        has_ensures = "ensures" in signature
        has_spec = has_requires or has_ensures

        if not has_spec:
            continue  # This isn't a Verus function

        # Find the matching closing brace for the function body
        brace_count = 1
        pos = brace_pos + 1
        body_end = brace_pos

        while pos < len(content) and brace_count > 0:
            if content[pos] == "{":
                brace_count += 1
            elif content[pos] == "}":
                brace_count -= 1
                if brace_count == 0:
                    body_end = pos
                    break
            pos += 1

        # Extract the function body
        body = content[brace_pos : body_end + 1]

        # Check if body contains 'assume'
        # Look for 'assume(' or 'assume ' patterns
        has_assume = bool(re.search(r"\bassume\s*\(", body))

        has_proof = has_spec and not has_assume

        return (has_spec, has_proof)

    # Probably what's happened is that we saw the function, but
    # it doesn't have a spec yet
    return (False, False)


@beartype
def extract_file_path_from_link(link: str, src_dir: Path) -> Path:
    """
    Extract the file path from a GitHub link.

    Example:
      https://github.com/dalek-cryptography/curve25519-dalek/tree/curve25519-4.1.3/curve25519-dalek/src/window.rs#L232
      -> src_dir/window.rs

    """
    assert link

    # Extract path after /src/
    match = re.search(r"/blob/([^/]+)/([^#]+)", link)

    assert match, link
    relative_path = match.group(2)

    file_path = src_dir / relative_path
    assert file_path.exists()
    return file_path



@beartype
def analyze_functions(csv_path: Path, src_dir: Path) -> Dict[str, Tuple[bool, bool]]:
    """
    Analyze all functions in the CSV and check their Verus status.

    Returns:
        Dict mapping link to (has_spec_verus, has_proof_verus)
    """
    # Read the CSV to get function names
    with open(csv_path, "r") as f:
        reader = csv.DictReader(f)
        rows = [row for row in reader]

    results = {}

    for row in rows:

        func_name = row["function_name"]

        # Try to get the specific file from the GitHub link first
        github_link = row["link"]
        target_file = extract_file_path_from_link(github_link, src_dir)
        print(f"Analyzing: {target_file} -> {func_name}")

        # Search only in the specific file mentioned in the CSV
        print(f"  Checking specific file: {target_file.name}")
        result = parse_function_in_file(target_file, func_name)
        has_spec, has_proof = result
        results[row["link"]] = (has_spec, has_proof)
        print(
            f"  Found in {target_file.name}: spec={has_spec}, proof={has_proof}"
        )

    return results


@beartype
def update_csv(csv_path: Path, results: Dict[str, Tuple[bool, bool]]):
    """Update the CSV file with Verus analysis results."""
    # Read the CSV
    rows = []
    with open(csv_path, "r") as f:
        reader = csv.DictReader(f)
        fieldnames = reader.fieldnames
        for row in reader:
            rows.append(row)

    # Update rows with results
    for row in rows:
        link = row["link"]
        if link in results:
            has_spec, has_proof = results[link]
            row["has_spec_verus"] = "yes" if has_spec else ""
            row["has_proof_verus"] = "yes" if has_proof else ""

    # Write the updated CSV back to the same file
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"\nCSV file updated: {csv_path}")

    # Print summary
    spec_count = sum(1 for _, (has_spec, _) in results.items() if has_spec)
    proof_count = sum(1 for _, (_, has_proof) in results.items() if has_proof)
    total = len(results)

    print("\nSummary:")
    print(f"  Total functions: {total}")
    print(
        f"  With Verus specs: {spec_count} ({round(spec_count * 100 / total) if total > 0 else 0}%)"
    )
    print(
        f"  With complete proofs: {proof_count} ({round(proof_count * 100 / total) if total > 0 else 0}%)"
    )


@beartype
def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Verus specs and proofs in curve25519-dalek functions"
    )
    parser.add_argument(
        "--csv",
        type=str,
        default="curve25519_functions.csv",
        help="CSV file name (default: curve25519_functions.csv)",
    )
    parser.add_argument(
        "--csv-path",
        type=str,
        help="Full path to CSV file (overrides --csv)",
    )
    args = parser.parse_args()

    # Set up paths
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent  # Go up one level from scripts/ to repo root
    outputs_dir = repo_root / "outputs"
    src_dir = repo_root

    # Determine CSV path
    if args.csv_path:
        csv_path = Path(args.csv_path)
        if not csv_path.exists():
            print(f"Error: CSV file not found at {csv_path}")
            return
    else:
        csv_path = outputs_dir / args.csv
        if not csv_path.exists():
            print(f"Error: CSV file not found at {csv_path}")
            print(f"Looked for: {args.csv} in {outputs_dir}")
            return

    if not src_dir.exists():
        print(f"Error: Source directory not found at {src_dir}")
        return

    print(f"Analyzing functions from: {csv_path}")
    print(f"Searching in: {src_dir}")
    print()

    # Analyze functions
    results = analyze_functions(csv_path, src_dir)

    # Update CSV
    update_csv(csv_path, results)


if __name__ == "__main__":
    main()
