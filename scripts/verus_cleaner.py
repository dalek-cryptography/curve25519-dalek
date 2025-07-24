#!/usr/bin/env python3

import sys
import re
import argparse
import subprocess
import os
import tempfile
import shutil
import uuid


def run_verus_verification(timeout):
    """
    Run Verus verification as described in CLAUDE.md.
    Returns True if verification passes, False otherwise.
    """
    try:
        # Change to curve25519-dalek directory and run verification
        result = subprocess.run(
            ['cargo', 'verus', 'verify', '--', '--multiple-errors', '20'],
            cwd='curve25519-dalek',
            capture_output=True,
            text=True,
            timeout=timeout
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        print(f"Verus verification timed out after {timeout} seconds", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error running Verus verification: {e}", file=sys.stderr)
        return False


def find_matching_lines(lines, start_line, end_line, regex_pattern):
    """
    Find all statements matching the pattern in the specified range.
    
    Returns:
        List of tuples (line_number, line_content) for matching statements
    """
    try:
        pattern = re.compile(regex_pattern)
    except re.error as e:
        print(f"Error: Invalid regex pattern: {e}", file=sys.stderr)
        return []
    
    matching_lines = []
    for i, line in enumerate(lines, 1):
        if start_line <= i <= end_line:
            if pattern.search(line.strip()):
                matching_lines.append((i, line))
    
    return matching_lines


def clean_statements(file_path, start_line, end_line, regex_pattern, timeout):
    """
    Systematically test removal of statements using Verus verification.
    
    Args:
        file_path: Path to the file to process
        start_line: Starting line number (1-indexed)  
        end_line: Ending line number (1-indexed, inclusive)
        regex_pattern: Regex pattern to match statements
        timeout: Timeout in seconds for Verus verification (default: 60)
    """
    # Validate file exists
    if not os.path.exists(file_path):
        print(f"Error: File '{file_path}' not found.", file=sys.stderr)
        return False
    
    # Read original file
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            original_lines = f.readlines()
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        return False
    
    # Create backup before any modifications
    unique_id = str(uuid.uuid4())
    file_name = os.path.basename(file_path)
    file_name_no_ext, file_ext = os.path.splitext(file_name)
    backup_path = f"/tmp/{file_name_no_ext}-{unique_id}{file_ext}"
    
    try:
        with open(backup_path, 'w', encoding='utf-8') as f:
            f.writelines(original_lines)
        print(f"Created backup at: {backup_path}")
        print()
    except Exception as e:
        print(f"Error creating backup: {e}", file=sys.stderr)
        return False
    
    # Validate line range
    if start_line < 1 or end_line < 1:
        print("Error: Line numbers must be >= 1", file=sys.stderr)
        return False
    
    if start_line > len(original_lines) or end_line > len(original_lines):
        print(f"Error: Line range exceeds file length ({len(original_lines)} lines)", file=sys.stderr)
        return False
    
    if start_line > end_line:
        print("Error: Start line must be <= end line", file=sys.stderr)
        return False
    
    # Find all statements in range
    matching_lines = find_matching_lines(original_lines, start_line, end_line, regex_pattern)
    
    if not matching_lines:
        print("No matching statements found in the specified range.")
        return True
    
    print(f"Found {len(matching_lines)} statements to test:")
    for line_num, line_content in matching_lines:
        print(f"  Line {line_num}: {line_content.strip()}")
    print()
    
    # Test each statement individually
    removed_statements = []
    kept_statements = []
    
    for line_num, line_content in matching_lines:
        print(f"Testing removal of statement at line {line_num}...")
        print(f"  Content: {line_content.strip()}")
        
        # Create modified content with this statement removed
        modified_lines = original_lines.copy()
        modified_lines.pop(line_num - 1)  # Remove the statement line (convert to 0-indexed)
        
        # Write modified content to file
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(modified_lines)
        except Exception as e:
            print(f"  Error writing modified file: {e}", file=sys.stderr)
            continue
        
        # Run Verus verification
        print("  Running Verus verification...")
        if run_verus_verification(timeout):
            print(f"  ✓ Verification passed - statement at line {line_num} is redundant")
            removed_statements.append((line_num, line_content))
            # Keep the file without this statement - update our working copy
            original_lines = modified_lines.copy()
            # Adjust line numbers for remaining statements
            for i in range(len(matching_lines)):
                if matching_lines[i][0] > line_num:
                    matching_lines[i] = (matching_lines[i][0] - 1, matching_lines[i][1])
        else:
            print(f"  ✗ Verification failed - statement at line {line_num} is necessary")
            kept_statements.append((line_num, line_content))
            # Restore original file
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.writelines(original_lines)
            except Exception as e:
                print(f"  Error restoring file: {e}", file=sys.stderr)
                return False
        
        print()
    
    # Summary
    print("=" * 60)
    print("CLEANING SUMMARY")
    print("=" * 60)
    print(f"Total statements tested: {len(matching_lines)}")
    print(f"Redundant statements removed: {len(removed_statements)}")
    print(f"Necessary statements kept: {len(kept_statements)}")
    
    if removed_statements:
        print("\nRemoved (redundant) statements:")
        for line_num, line_content in removed_statements:
            print(f"  Line {line_num}: {line_content.strip()}")
    
    if kept_statements:
        print("\nKept (necessary) statements:")
        for line_num, line_content in kept_statements:
            print(f"  Line {line_num}: {line_content.strip()}")

    print("Warning: This script works line by line and won't remove multi-line statements.")
    
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Systematically test removal of statements using Verus verification",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Usage:
  scripts/verus_cleaner.py <file> <start_line> <end_line> <regex_pattern> [--timeout SECONDS]

Examples:
  scripts/verus_cleaner.py curve25519-dalek/src/backend/serial/u64/field_verus.rs 100 200 '^[^/]*lemma'
  scripts/verus_cleaner.py curve25519-dalek/src/backend/serial/u64/scalar_verus.rs 50 150 "assert" --timeout 120
  
- For each matching statement in the range:
  1. Remove the statement from the file
  2. Run 'cargo verus verify -- --multiple-errors 20' 
  3. If verification passes: keep it removed (redundant)
  4. If verification fails: restore it (necessary)
        """
    )
    
    parser.add_argument('file', help='File to process (relative to project root)')
    parser.add_argument('start_line', type=int, help='Starting line number (1-indexed)')
    parser.add_argument('end_line', type=int, help='Ending line number (1-indexed, inclusive)')
    parser.add_argument('regex', help='Regex pattern to match statements')
    parser.add_argument('--timeout', type=int, default=60, help='Timeout in seconds for Verus verification (default: 60)')
    
    args = parser.parse_args()
    
    success = clean_statements(args.file, args.start_line, args.end_line, args.regex, args.timeout)
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
