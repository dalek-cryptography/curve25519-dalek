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
from typing import Dict, Tuple
from beartype import beartype


@beartype
def parse_function_in_file(
    file_path: Path, function_name: str
) -> Tuple[bool, bool, bool, int]:
    """
    Parse a Rust file to find a function and check if it has Verus specs and proofs.

    Returns:
        Tuple[bool, bool, bool, int]: (has_spec, has_proof, is_external_body, line_number)
        - has_spec: True if function has requires or ensures clauses
        - has_proof: True if has_spec and no assume in body
        - is_external_body: True if function has #[verifier::external_body]
        - line_number: Line number where the function is defined (1-indexed)

    TODO: Uncertain if this does the right thing if there are two functions with
    the same name in the same file
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

        # Check if this function is inside a comment block
        # Look backwards for /* or // to see if we're in a comment
        look_back_start = max(0, fn_start - 1000)
        preceding_text = content[look_back_start:fn_start]

        # Check for /* ... */ block comments
        last_block_open = preceding_text.rfind("/*")
        last_block_close = preceding_text.rfind("*/")
        if last_block_open > last_block_close:
            # We're inside a block comment, skip this match
            continue

        # Check for line comments - see if the function is on the same line as //
        last_newline = preceding_text.rfind("\n")
        if last_newline != -1:
            line_start = preceding_text[last_newline:]
            if "//" in line_start:
                # We're on a line with a // comment, skip this match
                continue

        # Find the function body by looking for the opening brace
        # For Verus functions with complex specs, we need a more robust approach
        # Look for the pattern that indicates the start of the function body

        # First, extract the entire function signature including specs
        signature_end = fn_start
        pos = fn_start
        paren_depth = 0
        brace_depth = 0
        found_opening_paren = False

        # Find the end of the function signature (including specs)
        while pos < len(content):
            char = content[pos]

            if char == "(":
                paren_depth += 1
                found_opening_paren = True
            elif char == ")":
                paren_depth -= 1
            elif char == "{":
                if found_opening_paren and paren_depth == 0 and brace_depth == 0:
                    # We've found the first brace at the top level after seeing the parameter list
                    # This should be the function body opening brace
                    signature_end = pos
                    break
                brace_depth += 1
            elif char == "}":
                brace_depth -= 1

            pos += 1

        brace_pos = signature_end if signature_end > fn_start else -1

        if brace_pos == -1:
            # Might be a trait definition without body
            continue

        # Look backwards from fn_start to find any attributes
        # Attributes appear before the function definition
        # Search backwards for the start of attributes (look for lines starting with #[)
        lines_before = content[:fn_start].split("\n")
        attr_lines = []

        # Skip the last line if it's not empty (it contains the beginning of the fn line)
        lines_to_check = (
            lines_before[:-1]
            if lines_before and lines_before[-1].strip()
            else lines_before
        )

        for line in reversed(lines_to_check):
            stripped = line.strip()
            if stripped.startswith("#["):
                attr_lines.insert(0, line)
            elif stripped and not stripped.startswith("//"):
                # Stop at first non-attribute, non-comment line (including closing braces)
                break

        attributes = "\n".join(attr_lines)

        # Extract the signature (between fn keyword and opening brace)
        signature = content[fn_start:brace_pos]

        # Check for requires or ensures in the signature
        # They must be the first non-whitespace on a line to avoid matching comments
        has_requires = bool(re.search(r"^\s*requires\b", signature, re.MULTILINE))
        has_ensures = bool(re.search(r"^\s*ensures\b", signature, re.MULTILINE))
        has_spec = has_requires or has_ensures

        # Check for verifier::external attributes early (before checking has_spec)
        has_verifier_external = bool(re.search(r"#\[verifier::external", attributes))

        # If neither specs nor external_body, skip this function
        if not has_spec and not has_verifier_external:
            continue  # This isn't a Verus-related function

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

        # Find the next function to determine the region boundary
        next_fn_pos = len(content)
        next_fn_match = re.search(
            r"(?:pub\s+)?(?:const\s+)?fn\s+", content[body_end + 1 :]
        )
        if next_fn_match:
            next_fn_pos = body_end + 1 + next_fn_match.start()

        # Extract the region from this fn to the next fn
        fn_region = content[fn_start:next_fn_pos]

        # Additional check: assume anywhere in the fn region (between this fn and next fn)
        # Check each line to exclude comments
        has_assume_in_region = False
        for line in fn_region.split("\n"):
            # Skip lines that are comments (starting with //)
            stripped = line.lstrip()
            if stripped.startswith("//"):
                continue
            # Check if line contains assume (outside of comments)
            # Remove inline comments first
            code_part = line.split("//")[0]
            if re.search(r"\bassume\b", code_part):
                has_assume_in_region = True
                break

        # In attributes: exec_allows_no_decreases_clause (external already checked above)
        has_no_decreases = bool(
            re.search(r"#\[verifier::exec_allows_no_decreases_clause\]", attributes)
        )

        has_proof = (
            has_spec
            and not has_assume_in_region
            and not has_verifier_external
            and not has_no_decreases
        )

        # If function has external_body, treat it as having a spec (even if no requires/ensures)
        has_spec_or_external = has_spec or has_verifier_external

        # Calculate line number (1-indexed)
        line_number = content[:fn_start].count('\n') + 1

        return (has_spec_or_external, has_proof, has_verifier_external, line_number)

    # Probably what's happened is that we saw the function, but
    # it doesn't have a spec yet
    # Return line 0 if we couldn't find the function properly
    return (False, False, False, 0)


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
def analyze_functions(
    csv_path: Path, src_dir: Path
) -> Dict[str, Tuple[bool, bool, bool, int, str]]:
    """
    Analyze all functions in the CSV and check their Verus status.

    Returns:
        Dict mapping old_link to (has_spec_verus, has_proof_verus, is_external_body, line_number, new_link)
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
        has_spec, has_proof, is_external_body, line_number = result
        
        # Update the link with the correct line number
        # Replace the line number in the link: #L123 -> #L{line_number}
        new_link = re.sub(r'#L\d+', f'#L{line_number}', github_link) if line_number > 0 else github_link
        
        results[github_link] = (has_spec, has_proof, is_external_body, line_number, new_link)
        ext_marker = " [external_body]" if is_external_body else ""
        print(
            f"  Found in {target_file.name}: spec={has_spec}, proof={has_proof}{ext_marker}, line={line_number}"
        )

    return results


@beartype
def update_links_to_main_branch(csv_path: Path):
    """Update all GitHub links in CSV to use 'main' branch instead of specific commit hash."""
    try:
        print("Updating links to use 'main' branch...")
        
        # Read the CSV
        rows = []
        with open(csv_path, "r") as f:
            reader = csv.DictReader(f)
            fieldnames = reader.fieldnames
            for row in reader:
                # Update the link to use 'main' branch
                old_link = row["link"]
                if old_link:
                    # Replace the commit hash with 'main'
                    # Pattern: /blob/{HASH}/ -> /blob/main/
                    new_link = re.sub(
                        r'/blob/[a-f0-9]+/',
                        '/blob/main/',
                        old_link
                    )
                    row["link"] = new_link
                rows.append(row)
        
        # Write back to CSV
        with open(csv_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        
        print("✓ Updated all links to use 'main' branch")
    except Exception as e:
        print(f"Warning: Could not update links: {e}")
        print("Continuing with existing links...")


@beartype
def update_csv(csv_path: Path, results: Dict[str, Tuple[bool, bool, bool, int, str]]):
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
        old_link = row["link"]
        if old_link in results:
            has_spec, has_proof, is_external_body, line_number, new_link = results[old_link]
            # Update link to include correct line number
            row["link"] = new_link
            # Use "ext" for functions with external_body, "yes" for regular specs
            if has_spec:
                row["has_spec_verus"] = "ext" if is_external_body else "yes"
            else:
                row["has_spec_verus"] = ""
            row["has_proof_verus"] = "yes" if has_proof else ""

    # Write the updated CSV back to the same file
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"\nCSV file updated: {csv_path}")

    # Print summary
    spec_count = sum(1 for _, (has_spec, _, _, _, _) in results.items() if has_spec)
    proof_count = sum(1 for _, (_, has_proof, _, _, _) in results.items() if has_proof)
    external_count = sum(
        1 for _, (has_spec, _, is_ext, _, _) in results.items() if has_spec and is_ext
    )
    full_spec_count = spec_count - external_count
    total = len(results)

    print("\nSummary:")
    print(f"  Total functions: {total}")
    print(
        f"  With Verus specs: {spec_count} ({round(spec_count * 100 / total) if total > 0 else 0}%)"
    )
    print(f"    - Full specs: {full_spec_count}")
    print(f"    - External body: {external_count}")
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

    # Update links to use 'main' branch
    update_links_to_main_branch(csv_path)
    print()

    # Analyze functions
    results = analyze_functions(csv_path, src_dir)

    # Update CSV
    update_csv(csv_path, results)


if __name__ == "__main__":
    main()
