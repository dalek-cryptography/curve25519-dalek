#!/usr/bin/env python3
"""
Script to detect newly verified Verus functions in git diff.
This script analyzes git diff output to find Verus functions that were added or modified.
"""

import re
import subprocess
import sys
from pathlib import Path


def get_git_diff(base_ref="origin/main"):
    """Get git diff output for Rust files."""
    try:
        result = subprocess.run(
            ["git", "diff", f"{base_ref}..HEAD", "--unified=3", "*.rs"],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running git diff: {e}", file=sys.stderr)
        return ""


def extract_added_verus_functions(diff_output):
    """Extract Verus function names from git diff output."""
    # Pattern to match added lines with Verus functions
    verus_block_pattern = re.compile(r'^\+.*verus!\s*\{', re.MULTILINE)
    function_pattern = re.compile(r'^\+.*fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', re.MULTILINE)
    
    functions = set()
    lines = diff_output.split('\n')
    
    in_added_verus_block = False
    for line in lines:
        # Check if we're entering a Verus block that was added
        if line.startswith('+') and 'verus!' in line and '{' in line:
            in_added_verus_block = True
            continue
        
        # Check if we're exiting a Verus block
        if in_added_verus_block and line.startswith('+') and '}' in line:
            in_added_verus_block = False
            continue
        
        # Look for function definitions in added lines within Verus blocks
        if in_added_verus_block and line.startswith('+'):
            match = re.search(r'fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', line)
            if match:
                func_name = match.group(1)
                # Filter out Verus-specific function types
                if not any(keyword in line for keyword in ['spec', 'proof', 'exec', 'open']):
                    functions.add(func_name)
    
    return list(functions)


def main():
    if len(sys.argv) > 1:
        base_ref = sys.argv[1]
    else:
        base_ref = "origin/main"
    
    print(f"Analyzing git diff against {base_ref}...", file=sys.stderr)
    
    diff_output = get_git_diff(base_ref)
    if not diff_output:
        print("No diff output found", file=sys.stderr)
        return 0
    
    functions = extract_added_verus_functions(diff_output)
    
    if functions:
        print("Found newly added Verus functions:", file=sys.stderr)
        for func in functions:
            print(func)
    else:
        print("No newly added Verus functions found", file=sys.stderr)
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
