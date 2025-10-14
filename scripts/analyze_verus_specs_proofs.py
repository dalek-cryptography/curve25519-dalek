#!/usr/bin/env python3
"""
Analyze Verus specs and proofs in curve25519-dalek source code.
Updates the CSV to mark which functions have Verus specs and/or proofs.
"""

import argparse
import csv
import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional


def extract_function_name(function_path: str) -> str:
    """
    Extract the actual function name from the CSV function_path format.

    Examples:
      - "backend/serial/u64/field/impl#[FieldElement51]as_bytes()." -> "as_bytes"
      - "scalar/read_le_u64_into()." -> "read_le_u64_into"
      - "backend/serial/u64/scalar/m()." -> "m"
    """
    # Remove trailing dot
    function_path = function_path.rstrip(".")

    # Extract the last part after / or ]
    if "]" in function_path:
        # Handle impl#[Type]function_name format
        parts = function_path.split("]")
        if len(parts) > 1:
            name_part = parts[-1]
        else:
            name_part = function_path
    else:
        # Handle simple path/function_name format
        name_part = function_path.split("/")[-1]

    # Remove parentheses and everything after them
    if "(" in name_part:
        name_part = name_part.split("(")[0]

    return name_part.strip()


def find_rust_files(src_dir: Path) -> List[Path]:
    """Find all Rust source files in the directory."""
    return list(src_dir.rglob("*.rs"))


def parse_function_in_file(
    file_path: Path, function_name: str
) -> Optional[Tuple[bool, bool]]:
    """
    Parse a Rust file to find a function and check if it has Verus specs and proofs.

    Returns:
        Tuple[bool, bool]: (has_spec, has_proof) or None if function not found
        - has_spec: True if function has requires or ensures clauses
        - has_proof: True if has_spec and no assume in body
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return None

    # Pattern to match function definitions
    # Matches: fn function_name, pub fn function_name, pub const fn function_name, etc.
    # This regex looks for function definitions
    fn_pattern = (
        r"(?:pub\s+)?(?:const\s+)?fn\s+" + re.escape(function_name) + r"\s*[<\(]"
    )

    # Find all occurrences of the function
    matches = list(re.finditer(fn_pattern, content))

    if not matches:
        return None

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

    return None


def extract_file_path_from_link(link: str, src_dir: Path) -> Optional[Path]:
    """
    Extract the file path from a GitHub link.

    Example:
      https://github.com/dalek-cryptography/curve25519-dalek/tree/curve25519-4.1.3/curve25519-dalek/src/window.rs#L232
      -> src_dir/window.rs

    Special case: field.rs -> field_verus.rs (Verus work done separately)
    """
    if not link:
        return None

    # Extract path after /src/
    match = re.search(r"/src/([^#]+)", link)
    if match:
        relative_path = match.group(1)

        # Special case: look in field_verus.rs instead of backend/serial/u64/field.rs
        if "backend/serial/u64/field.rs" in relative_path:
            relative_path = relative_path.replace("field.rs", "field_verus.rs")

        file_path = src_dir / relative_path
        if file_path.exists():
            return file_path

    return None


def analyze_functions(csv_path: Path, src_dir: Path) -> Dict[str, Tuple[bool, bool]]:
    """
    Analyze all functions in the CSV and check their Verus status.

    Returns:
        Dict mapping function_path to (has_spec_verus, has_proof_verus)
    """
    # Read the CSV to get function names
    with open(csv_path, "r") as f:
        reader = csv.DictReader(f)
        functions = [(row["function_name"], row) for row in reader]

    # Find all Rust files (as fallback)
    rust_files = find_rust_files(src_dir)
    print(f"Found {len(rust_files)} Rust source files")

    results = {}

    for func_path, row in functions:
        if not func_path:
            continue

        func_name = extract_function_name(func_path)
        print(f"Analyzing: {func_path} -> {func_name}")

        # Try to get the specific file from the GitHub link first
        github_link = row.get("link", "")
        target_file = extract_file_path_from_link(github_link, src_dir)

        if target_file:
            # Search only in the specific file mentioned in the CSV
            print(f"  Checking specific file: {target_file.name}")
            result = parse_function_in_file(target_file, func_name)
            if result is not None:
                has_spec, has_proof = result
                results[func_path] = (has_spec, has_proof)
                print(
                    f"  Found in {target_file.name}: spec={has_spec}, proof={has_proof}"
                )
            else:
                # Function not found or doesn't have Verus specs
                results[func_path] = (False, False)
                print("  Not found or no Verus spec")
        else:
            # Fallback: search for the function in all Rust files (old behavior)
            print("  No specific file link, searching all files...")
            found = False
            for rust_file in rust_files:
                result = parse_function_in_file(rust_file, func_name)
                if result is not None:
                    has_spec, has_proof = result
                    results[func_path] = (has_spec, has_proof)
                    print(
                        f"  Found in {rust_file.name}: spec={has_spec}, proof={has_proof}"
                    )
                    found = True
                    break

            if not found:
                # Function not found or doesn't have Verus specs
                results[func_path] = (False, False)
                print("  Not found or no Verus spec")

    return results


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
        func_path = row["function_name"]
        if func_path in results:
            has_spec, has_proof = results[func_path]
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
    src_dir = repo_root / "curve25519-dalek" / "src"

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
