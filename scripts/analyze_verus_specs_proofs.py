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
import subprocess
from pathlib import Path
from typing import Dict, Tuple, Optional
from beartype import beartype

# Constants
CRATE_NAME = "curve25519_dalek"
CRATE_DIR = "curve25519-dalek"
GITHUB_REPO = "Beneficial-AI-Foundation/dalek-lite"

# Special module mappings (modules with non-standard file locations)
SPECIAL_MODULES = {
    "build": lambda src_dir: src_dir / CRATE_DIR / "build.rs",
}


@beartype
def extract_impl_signature(content: str, fn_start: int) -> Optional[str]:
    """
    Extract the full impl block signature for a function.

    For example, if the function is inside:
        impl Identity for ProjectivePoint {
    Returns "Identity for ProjectivePoint"

    For trait implementations like:
        impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
    Returns "Add<&'b Scalar> for &'a Scalar"

    For inherent implementations:
        impl Scalar {
    Returns "Scalar"
    """
    # Look backwards from fn_start to find the impl block
    look_back = content[:fn_start]
    lines = look_back.split("\n")

    # Search backwards for impl block
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()

        # Stop at verus! blocks or module boundaries
        if line.startswith("verus!") or line.startswith("mod "):
            break

        # Look for impl blocks
        if line.startswith("impl"):
            # Extract everything between 'impl' and '{'
            # Pattern: impl<...> TraitName<...> for TypeName { or impl TypeName {
            match = re.search(r"impl\s*(?:<[^>]+>)?\s*(.+?)\s*\{", line)
            if match:
                impl_part = match.group(1).strip()
                # Note: lifetime params are cleaned up later in normalize_impl()
                return impl_part

    return None


@beartype
def extract_impl_context(content: str, fn_start: int) -> Optional[str]:
    """
    Extract the impl block context for a function.

    For example, if the function is inside:
        impl Identity for ProjectivePoint {
    Returns "ProjectivePoint"

    For trait implementations like:
        impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
    Returns "Scalar" (the type being implemented for)
    """
    # Look backwards from fn_start to find the impl block
    look_back = content[:fn_start]
    lines = look_back.split("\n")

    # Search backwards for impl block
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()

        # Stop at verus! blocks or module boundaries
        if line.startswith("verus!") or line.startswith("mod "):
            break

        # Look for impl blocks
        if line.startswith("impl"):
            # Try to extract the type being implemented for
            # Pattern 1: impl TraitName for TypeName {
            match = re.search(
                r"impl\s+(?:<[^>]+>)?\s*\w+\s+for\s+([&\']*)([A-Za-z0-9_]+)", line
            )
            if match:
                return match.group(2)

            # Pattern 2: impl TypeName {  or  impl<...> TypeName {
            match = re.search(r"impl\s*(?:<[^>]+>)?\s+([A-Za-z0-9_]+)\s*\{", line)
            if match:
                return match.group(1)

    return None


@beartype
def extract_module_from_path(file_path: Path, repo_root: Path) -> str:
    """
    Extract module path from file path.

    Example:
        curve25519-dalek/src/backend/serial/curve_models/mod.rs
        -> curve25519_dalek::backend::serial::curve_models

        curve25519-dalek/src/scalar.rs
        -> curve25519_dalek::scalar
    """
    try:
        # Get relative path from repo root
        rel_path = file_path.relative_to(repo_root)

        # Remove curve25519-dalek/ prefix and src/ prefix
        parts = list(rel_path.parts)

        # Skip "curve25519-dalek" and "src"
        module_parts = []
        skip_parts = {"curve25519-dalek", "src"}

        for part in parts:
            if part in skip_parts:
                continue
            # Remove .rs extension or mod.rs
            if part.endswith(".rs"):
                if part == "mod.rs":
                    continue
                part = part[:-3]
            module_parts.append(part.replace("-", "_"))

        # Prepend crate name
        return "curve25519_dalek::" + "::".join(module_parts)
    except Exception:
        return "curve25519_dalek"


@beartype
def parse_function_in_file(
    file_path: Path, function_name: str, old_link: str = "", impl_block: str = ""
) -> Tuple[bool, bool, bool, int, str]:
    """
    Parse a Rust file to find a function and check if it has Verus specs and proofs.

    Args:
        file_path: Path to the Rust source file
        function_name: Bare function name (without type prefix or signature)
        old_link: Optional GitHub link with line number hint
        impl_block: Optional impl block context for disambiguation (e.g., "Add for FieldElement51")

    Returns:
        Tuple[bool, bool, bool, int, str]: (has_spec, has_proof, is_external_body, line_number, qualified_name)
        - has_spec: True if function has requires or ensures clauses
        - has_proof: True if has_spec and no assume in body
        - is_external_body: True if function has #[verifier::external_body]
        - line_number: Line number where the function is defined (1-indexed)
        - qualified_name: Function name with impl context (e.g., "ProjectivePoint::identity")
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

    # If we have an old link with a line number, use it to find the closest match
    target_line = None
    if old_link:
        line_match = re.search(r"#L(\d+)", old_link)
        if line_match:
            target_line = int(line_match.group(1))

    # If there are multiple matches and we have a target line, sort by proximity to target
    if target_line and len(matches) > 1:
        matches_with_lines = []
        for match in matches:
            line_num = content[: match.start()].count("\n") + 1
            distance = abs(line_num - target_line)
            matches_with_lines.append((distance, match))
        matches_with_lines.sort(key=lambda x: x[0])
        matches = [m[1] for m in matches_with_lines]

    # If we have impl_block for disambiguation and multiple matches, filter by impl context
    if impl_block and len(matches) > 1:
        filtered_matches = []
        for match in matches:
            fn_start = match.start()
            found_impl_sig = extract_impl_signature(content, fn_start)
            if found_impl_sig:
                # Normalize both for comparison (remove lifetimes but preserve &)
                def normalize_impl(s):
                    # Remove lifetime annotations while preserving & references
                    # Pattern 1: <'a> → "" (standalone lifetime generics like Deserialize<'de>)
                    # Pattern 2: 'a → "" (lifetimes in mixed contexts like &'b Scalar → &Scalar)
                    # Both patterns together ensure consistent normalization for matching
                    s = re.sub(r"<'\w+>", "", s)
                    s = re.sub(r"'\w+\b", "", s)
                    # Remove space after & to normalize "&'a Scalar" → "&Scalar" and "&Scalar" → "&Scalar"
                    s = re.sub(r"&\s+", "&", s)
                    return " ".join(s.split())

                norm_found = normalize_impl(found_impl_sig)
                norm_expected = normalize_impl(impl_block)

                # Check if they match exactly
                if norm_found == norm_expected:
                    filtered_matches.append(match)
                    continue

                # Check for reference vs owned type distinction
                # "Neg for &EdwardsPoint" vs "Neg for EdwardsPoint"
                # Only applies when trait names match (e.g., both are "Neg")
                if " for " in impl_block and " for " in norm_found:
                    expected_trait = impl_block.split(" for ")[0].strip()
                    found_trait = norm_found.split(" for ")[0].strip()
                    # Extract base trait name (e.g., "Neg" from "Neg", "From<u8>" stays as is)
                    expected_trait_base = expected_trait.split("<")[0]
                    found_trait_base = found_trait.split("<")[0]

                    # Only do ref vs owned check if traits match and have no type params
                    # (e.g., Neg for &T vs Neg for T, not From<u8> vs From<u16>)
                    if (
                        expected_trait_base == found_trait_base
                        and "<" not in expected_trait
                    ):
                        expected_type = impl_block.split(" for ")[-1].strip()
                        found_type = norm_found.split(" for ")[-1].strip()
                        expected_is_ref = expected_type.startswith("&")
                        found_is_ref = found_type.startswith("&")
                        if expected_is_ref == found_is_ref:
                            expected_base = expected_type.lstrip("&").strip()
                            found_base = found_type.lstrip("&").strip()
                            if expected_base == found_base:
                                filtered_matches.append(match)
                                continue
        if filtered_matches:
            matches = filtered_matches

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
            # Might be a trait method declaration without body (ends with semicolon)
            # Calculate line number for trait methods too
            line_number = content[:fn_start].count("\n") + 1
            # Trait methods don't have specs/proofs, just return line number
            # Try to extract impl context
            impl_context = extract_impl_context(content, fn_start)
            qualified_name = (
                f"{impl_context}::{function_name}" if impl_context else function_name
            )
            return (False, False, False, line_number, qualified_name)

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

        # Calculate line number for ALL functions (even those without specs)
        # This ensures CSV links are always up-to-date
        line_number = content[:fn_start].count("\n") + 1

        # Extract impl context for qualified name
        impl_context = extract_impl_context(content, fn_start)
        qualified_name = (
            f"{impl_context}::{function_name}" if impl_context else function_name
        )

        # If neither specs nor external_body, return early with just the line number
        if not has_spec and not has_verifier_external:
            return (False, False, False, line_number, qualified_name)

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

        # Line number and qualified name were already calculated earlier
        return (
            has_spec_or_external,
            has_proof,
            has_verifier_external,
            line_number,
            qualified_name,
        )

    # Probably what's happened is that we saw the function, but
    # it doesn't have a spec yet
    # Return line 0 if we couldn't find the function properly
    # Try to get impl context even if function not found
    impl_context = extract_impl_context(content, 0) if matches else None
    qualified_name = (
        f"{impl_context}::{function_name}" if impl_context else function_name
    )
    return (False, False, False, 0, qualified_name)


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
def discover_function_in_module(
    qualified_func: str, module: str, src_dir: Path, impl_block: str = ""
) -> Optional[Tuple[Path, int, str]]:
    """
    Discover a function in the codebase given its qualified name and module.

    Args:
        qualified_func: Function name, possibly qualified (e.g., "FieldElement51::mul(args)" or "mul")
        module: Module path (e.g., "curve25519_dalek::backend::serial::u64::field")
        src_dir: Root source directory
        impl_block: Optional impl block context for disambiguation (e.g., "Add for FieldElement51")

    Returns:
        Tuple of (file_path, line_number, github_link) if found, None otherwise
    """
    # Convert module path to file path
    # e.g., "curve25519_dalek::backend::serial::u64::field" -> "curve25519-dalek/src/backend/serial/u64/field.rs"
    module_stripped = module.replace(f"{CRATE_NAME}::", "")
    module_parts = module_stripped.split("::") if module_stripped else []

    # Handle special module cases (non-standard file locations)
    possible_paths = []
    module_key = module_parts[0] if module_parts else None
    if module_key in SPECIAL_MODULES:
        possible_paths.append(SPECIAL_MODULES[module_key](src_dir))
    else:
        # Try both .rs file and mod.rs
        possible_paths.extend(
            [
                src_dir
                / CRATE_DIR
                / "src"
                / "/".join(module_parts[:-1])
                / f"{module_parts[-1]}.rs",
                src_dir / CRATE_DIR / "src" / "/".join(module_parts) / "mod.rs",
            ]
        )

    # Extract just the function name (without Type:: prefix and signature if present)
    func_part = (
        qualified_func.split("::")[-1] if "::" in qualified_func else qualified_func
    )
    # Strip signature if present: "method(args)" -> "method"
    func_name = func_part.split("(")[0] if "(" in func_part else func_part

    for file_path in possible_paths:
        if not file_path.exists():
            continue

        # Try to find the function in this file, passing impl_block for disambiguation
        result = parse_function_in_file(file_path, func_name, "", impl_block)
        has_spec, has_proof, is_external_body, line_number, found_qualified = result
        if line_number > 0:
            # Generate GitHub link
            relative_path = file_path.relative_to(src_dir)
            github_link = f"https://github.com/{GITHUB_REPO}/blob/main/{relative_path}#L{line_number}"
            return (file_path, line_number, github_link)

    return None


@beartype
def analyze_functions(
    seed_path: Path, src_dir: Path
) -> Dict[str, Tuple[bool, bool, bool, int, str, str, str, str]]:
    """
    Analyze all functions in the seed file and check their Verus status.

    Args:
        seed_path: Path to functions_to_track.csv (function, module, impl_block columns)
        src_dir: Root source directory

    Returns:
        Dict mapping function_module_impl_key to (has_spec, has_proof, is_external_body, line_number, github_link, qualified_name, module_name, impl_block)
    """
    # Read the seed CSV to get function names and modules
    with open(seed_path, "r") as f:
        reader = csv.DictReader(f)
        rows = [row for row in reader]

    results = {}

    # Keep track of functions we've seen to detect macro-generated duplicates
    seen_functions = {}

    for row in rows:
        qualified_func = row["function"]
        module = row["module"]
        impl_block = row.get("impl_block", "")  # New column for disambiguation

        # Extract just the function name for searching
        # Handle new format: "Type::method(signature)" -> extract "method"
        func_part = (
            qualified_func.split("::")[-1] if "::" in qualified_func else qualified_func
        )
        # Strip signature if present: "method(args)" -> "method"
        func_name = func_part.split("(")[0] if "(" in func_part else func_part

        print(f"Discovering: {qualified_func} in {module}")

        # Discover the function in the codebase
        discovery = discover_function_in_module(
            qualified_func, module, src_dir, impl_block
        )
        if not discovery:
            print("  WARNING: Function not found in codebase, skipping")
            continue

        target_file, line_number, github_link = discovery

        # Re-analyze to get full details (spec, proof, etc.)
        result = parse_function_in_file(target_file, func_name, github_link, impl_block)
        has_spec, has_proof, is_external_body, line_number, found_qualified = result
        if line_number == 0:
            print("  WARNING: Could not re-analyze function, skipping")
            continue

        # Check for macro-generated duplicates (same file, same function name, same line, same impl_block)
        func_key = f"{target_file}::{found_qualified}::{line_number}::{impl_block}"
        if func_key in seen_functions:
            print(
                f"  Skipping duplicate (macro-generated): {found_qualified} at line {line_number}"
            )
            continue
        seen_functions[func_key] = True

        # Use a unique key for results (function + module + impl_block)
        result_key = f"{qualified_func}::{module}::{impl_block}"
        results[result_key] = (
            has_spec,
            has_proof,
            is_external_body,
            line_number,
            github_link,  # Use the link we generated during discovery
            qualified_func,  # Use the qualified name from seed file
            module,  # Use the module from seed file
            impl_block,  # Include impl_block for disambiguation
        )
        ext_marker = " [external_body]" if is_external_body else ""
        print(f"  Found: {qualified_func} in module {module}")
        print(f"    spec={has_spec}, proof={has_proof}{ext_marker}, line={line_number}")

    return results


@beartype
def update_links_to_main_branch(csv_path: Path):
    """Update all GitHub links in CSV to use 'main' branch instead of specific commit hash.

    Only updates links if the file exists on main to avoid 404 errors.
    """
    try:
        print("Updating links to use 'main' branch...")

        # Read the CSV
        rows = []
        updated_count = 0
        skipped_count = 0

        with open(csv_path, "r") as f:
            reader = csv.DictReader(f)
            fieldnames = reader.fieldnames
            for row in reader:
                # Update the link to use 'main' branch
                old_link = row["link"]
                if old_link:
                    # Extract file path from GitHub link
                    # Pattern: https://github.com/.../blob/{HASH}/path/to/file.rs#L123
                    match = re.search(r"/blob/[a-f0-9]+/(.+?)(?:#|$)", old_link)
                    if match:
                        file_path = match.group(1)
                        # Remove line number if present
                        file_path = file_path.split("#")[0]

                        # Check if file exists on main branch
                        try:
                            result = subprocess.run(
                                ["git", "cat-file", "-e", f"main:{file_path}"],
                                cwd=csv_path.parent.parent,  # repo root
                                capture_output=True,
                                timeout=5,
                            )

                            if result.returncode == 0:
                                # File exists on main, safe to update link
                                new_link = re.sub(
                                    r"/blob/[a-f0-9]+/", "/blob/main/", old_link
                                )
                                row["link"] = new_link
                                updated_count += 1
                            else:
                                # File doesn't exist on main, keep original link
                                skipped_count += 1
                        except (subprocess.TimeoutExpired, subprocess.SubprocessError):
                            # If git check fails, keep original link to be safe
                            skipped_count += 1
                    else:
                        # Couldn't parse link, keep original
                        pass
                rows.append(row)

        # Write back to CSV
        with open(csv_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)

        print(f"✓ Updated {updated_count} links to use 'main' branch")
        if skipped_count > 0:
            print(f"  Skipped {skipped_count} links (file not on main branch)")
    except Exception as e:
        print(f"Warning: Could not update links: {e}")
        print("Continuing with existing links...")


@beartype
def update_csv(
    csv_path: Path, results: Dict[str, Tuple[bool, bool, bool, int, str, str, str, str]]
):
    """Generate the CSV file with Verus analysis results."""
    # CSV format
    fieldnames = ["function", "module", "link", "has_spec", "has_proof"]

    # Build rows from results
    new_rows = []
    for result_key, (
        has_spec,
        has_proof,
        is_external_body,
        line_number,
        github_link,
        qualified_name,
        module_name,
        impl_block,
    ) in results.items():
        new_row = {
            "function": qualified_name,
            "module": module_name,
            "link": github_link,
            # Use "ext" for functions with external_body, "yes" for regular specs
            "has_spec": "ext" if is_external_body else ("yes" if has_spec else ""),
            "has_proof": "yes" if has_proof else "",
        }
        new_rows.append(new_row)

    # Write the CSV
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(new_rows)

    print(f"\nCSV file updated: {csv_path}")

    # Print summary
    spec_count = sum(
        1 for _, (has_spec, _, _, _, _, _, _, _) in results.items() if has_spec
    )
    proof_count = sum(
        1 for _, (_, has_proof, _, _, _, _, _, _) in results.items() if has_proof
    )
    external_count = sum(
        1
        for _, (has_spec, _, is_ext, _, _, _, _, _) in results.items()
        if has_spec and is_ext
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
        description="Generate CSV with Verus specs/proofs status from seed file"
    )
    parser.add_argument(
        "--seed",
        type=str,
        default="functions_to_track.csv",
        help="Seed file name (default: functions_to_track.csv)",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="outputs/curve25519_functions.csv",
        help="Output CSV file path (default: outputs/curve25519_functions.csv)",
    )
    args = parser.parse_args()

    # Set up paths
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent  # Go up one level from scripts/ to repo root
    seed_path = repo_root / args.seed
    output_path = repo_root / args.output
    src_dir = repo_root

    # Check seed file exists
    if not seed_path.exists():
        print(f"Error: Seed file not found at {seed_path}")
        return

    if not src_dir.exists():
        print(f"Error: Source directory not found at {src_dir}")
        return

    print(f"Reading seed file: {seed_path}")
    print(f"Will generate CSV at: {output_path}")
    print(f"Searching in: {src_dir}")
    print()

    # Analyze functions from seed file
    results = analyze_functions(seed_path, src_dir)

    # Generate output CSV
    output_path.parent.mkdir(parents=True, exist_ok=True)
    update_csv(output_path, results)


if __name__ == "__main__":
    main()
