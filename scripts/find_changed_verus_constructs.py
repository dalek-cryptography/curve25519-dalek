#!/usr/bin/env python3
"""
Script to detect changed (newly added or modified) Verus constructs in git diff.
This script analyzes git diff output to find Verus functions that were added or modified.
"""

import re
import subprocess
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Set, List, Dict, Optional, Tuple


@dataclass
class DiffContext:
    """Tracks the current context while parsing a diff"""
    current_file: Optional[str] = None
    in_verus_block: bool = False
    current_function: Optional[str] = None
    functions_with_changes: Set[str] = None
    
    def __post_init__(self):
        if self.functions_with_changes is None:
            self.functions_with_changes = set()


def get_git_diff(base_ref="origin/main"):
    """Get git diff output for Rust files."""
    try:
        # First, get the repository root
        root_result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True
        )
        repo_root = root_result.stdout.strip()
        print(f"DEBUG: Repository root: {repo_root}", file=sys.stderr)
        
        # Get list of all changed Rust files first
        changed_files_result = subprocess.run(
            ["git", "diff", "--name-only", f"{base_ref}..HEAD"],
            capture_output=True,
            text=True,
            check=True,
            cwd=repo_root
        )
        
        all_changed_files = changed_files_result.stdout.strip().split('\n') if changed_files_result.stdout.strip() else []
        rust_files = [f for f in all_changed_files if f.endswith('.rs')]
        
        print(f"DEBUG: Found {len(rust_files)} changed Rust files:", file=sys.stderr)
        for f in rust_files[:5]:  # Show first 5
            print(f"  - {f}", file=sys.stderr)
        
        if not rust_files:
            print("DEBUG: No Rust files changed, returning empty diff", file=sys.stderr)
            return ""
        
        # Get diff with more context lines to better understand function boundaries
        cmd = ["git", "diff", f"{base_ref}..HEAD", "--unified=10", "--"] + rust_files
        print(f"DEBUG: Running command: git diff {base_ref}..HEAD --unified=10 -- [... {len(rust_files)} rust files ...]", file=sys.stderr)
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True,
            cwd=repo_root
        )
        print(f"DEBUG: Git diff returned {len(result.stdout)} characters", file=sys.stderr)
        if result.stdout:
            print(f"DEBUG: First 500 chars of diff:\n{result.stdout[:500]}", file=sys.stderr)
        
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running git diff: {e}", file=sys.stderr)
        print(f"DEBUG: Git diff stderr: {e.stderr}", file=sys.stderr)
        return ""


def is_verus_function(line: str) -> bool:
    """Check if a line contains a Verus function definition."""
    # Match various Verus function patterns
    patterns = [
        r'(?:pub\s+)?(?:proof\s+|spec\s+|exec\s+|open\s+|closed\s+)?fn\s+',
        r'proof\s*\{',  # proof blocks
    ]
    return any(re.search(pattern, line) for pattern in patterns)


def extract_function_name(line: str) -> Optional[str]:
    """Extract function name from a line if it contains a function definition."""
    match = re.search(r'(?:pub\s+)?(?:proof\s+|spec\s+|exec\s+|open\s+|closed\s+)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[(<]', line)
    if match:
        return match.group(1)
    return None


def has_verus_annotation(lines: List[str], start_idx: int) -> bool:
    """Check if a function has Verus annotations (requires/ensures) in the next few lines."""
    verus_keywords = ['requires', 'ensures', 'decreases', 'invariant', 'recommends']
    look_ahead = 5
    
    for i in range(start_idx + 1, min(len(lines), start_idx + look_ahead + 1)):
        line = lines[i].strip()
        if any(keyword in line for keyword in verus_keywords):
            return True
        # Stop if we hit the function body
        if '{' in line and not line.strip().startswith('//'):
            break
    
    return False


def find_enclosing_function(lines: List[str], change_idx: int) -> Optional[str]:
    """
    Find the function that encloses a change by looking backwards from the change line.
    This helps identify which function contains modifications.
    """
    # Look backwards for function definition
    for i in range(change_idx - 1, max(0, change_idx - 50), -1):
        line = lines[i]
        # Skip diff markers
        if line.startswith(('+++', '---', '@@')):
            continue
        
        # Remove diff prefix if present
        clean_line = line[1:] if line and line[0] in ['+', '-', ' '] else line
        
        # Check for function definition
        func_name = extract_function_name(clean_line)
        if func_name:
            return func_name
    
    return None


def is_inside_verus_context(lines: List[str], line_idx: int) -> bool:
    """Check if a line is inside a verus! block by looking backwards and forwards."""
    # Look backwards for verus! block start
    verus_depth = 0
    for i in range(line_idx, -1, -1):
        line = lines[i]
        clean_line = line[1:] if line and line[0] in ['+', '-', ' '] else line
        
        if '} // verus!' in clean_line:
            verus_depth -= 1
        if 'verus!' in clean_line and '{' in clean_line:
            verus_depth += 1
            if verus_depth > 0:
                return True
    
    return False


def has_verus_syntax_in_function(lines: List[str], func_name: str, all_functions_in_diff: Dict[str, Tuple[int, bool]]) -> bool:
    """Check if a function contains Verus-specific syntax in its body."""
    if func_name not in all_functions_in_diff:
        return False
    
    func_def_line, _ = all_functions_in_diff[func_name]
    
    # Look for Verus-specific patterns in the function body
    verus_patterns = [
        r'assert\s*\([^)]+\)\s*by\s*\(',  # assert(...) by (...)
        r'proof\s*\{',                    # proof { ... }
        r'requires\s',                    # requires clause
        r'ensures\s',                     # ensures clause
        r'decreases\s',                   # decreases clause
        r'invariant\s',                   # invariant clause
        r'recommends\s',                  # recommends clause
        r'\bspec\b',                      # spec keyword
        r'\bproof\b',                     # proof keyword (in context)
        r'\bexec\b',                      # exec keyword
        r'broadcast\s+use',               # broadcast use
        r'assume\s*\(',                   # assume(...)
    ]
    
    # Search from function definition until next function or end of scope
    search_end = len(lines)
    brace_count = 0
    found_opening_brace = False
    
    # Find the end of this function by counting braces
    for i in range(func_def_line, len(lines)):
        line = lines[i]
        clean_line = line[1:] if line and line[0] in ['+', '-', ' '] else line
        
        # Count braces to find function end
        for char in clean_line:
            if char == '{':
                brace_count += 1
                found_opening_brace = True
            elif char == '}':
                brace_count -= 1
                if found_opening_brace and brace_count == 0:
                    search_end = i + 1
                    break
        
        if found_opening_brace and brace_count == 0:
            break
    
    # Search for Verus patterns in the function body
    for i in range(func_def_line, search_end):
        line = lines[i]
        clean_line = line[1:] if line and line[0] in ['+', '-', ' '] else line
        
        for pattern in verus_patterns:
            if re.search(pattern, clean_line):
                return True
    
    return False


def extract_changed_verus_constructs(diff_output: str) -> Dict[str, List[str]]:
    """Extract Verus constructs (functions) that were added or modified from git diff output."""
    constructs = {
        'added': set(),
        'modified': set(), 
        'all': set()
    }
    
    lines = diff_output.split('\n')
    changed_functions = set()
    all_functions_in_diff = {}  # func_name -> (line_idx, is_new)
    
    print(f"DEBUG: Processing {len(lines)} lines of diff", file=sys.stderr)
    
    # First, collect all function definitions in the diff
    for i, line in enumerate(lines):
        # Skip file headers
        if line.startswith(('+++', '---', '@@')):
            continue
            
        clean_line = line[1:] if line and line[0] in ['+', '-', ' '] else line
        func_name = extract_function_name(clean_line)
        
        if func_name:
            is_new = line.startswith('+')
            all_functions_in_diff[func_name] = (i, is_new)
            print(f"DEBUG: Found function '{func_name}' at line {i} (new={is_new})", file=sys.stderr)
    
    # Now find all lines with actual changes (+ or -)
    for i, line in enumerate(lines):
        # Skip headers and look for actual code changes
        if not line.startswith(('+', '-')) or line.startswith(('+++', '---')):
            continue
        
        # This is a changed line - find the enclosing function
        enclosing_func = None
        
        # Look backwards for the nearest function definition
        for j in range(i, -1, -1):
            check_line = lines[j]
            if check_line.startswith(('+++', '---', '@@')):
                continue
                
            clean_line = check_line[1:] if check_line and check_line[0] in ['+', '-', ' '] else check_line
            func_name = extract_function_name(clean_line)
            
            if func_name:
                enclosing_func = func_name
                print(f"DEBUG: Change at line {i} is inside function '{func_name}'", file=sys.stderr)
                break
        
        if enclosing_func:
            # Check if this function is in a Verus context
            is_verus = False
            
            # Check 1: Is the function inside a verus! block?
            if is_inside_verus_context(lines, i):
                is_verus = True
                print(f"DEBUG: Function '{enclosing_func}' is inside verus! block", file=sys.stderr)
            
            # Check 2: Does the function have Verus annotations?
            func_def_line = all_functions_in_diff.get(enclosing_func, (None, False))[0]
            if func_def_line is not None and has_verus_annotation(lines, func_def_line):
                is_verus = True
                print(f"DEBUG: Function '{enclosing_func}' has Verus annotations", file=sys.stderr)
            
            # Check 3: Is it a proof/spec/exec function?
            if func_def_line is not None:
                func_line = lines[func_def_line]
                clean_func_line = func_line[1:] if func_line and func_line[0] in ['+', '-', ' '] else func_line
                if re.search(r'(?:proof|spec|exec|open|closed)\s+fn', clean_func_line):
                    is_verus = True
                    print(f"DEBUG: Function '{enclosing_func}' is a proof/spec/exec function", file=sys.stderr)
            
            # Check 4: Does the function contain Verus-specific syntax?
            if not is_verus and has_verus_syntax_in_function(lines, enclosing_func, all_functions_in_diff):
                is_verus = True
                print(f"DEBUG: Function '{enclosing_func}' contains Verus-specific syntax", file=sys.stderr)
            
            if is_verus:
                changed_functions.add(enclosing_func)
    
    # Categorize functions
    for func_name in changed_functions:
        if func_name in all_functions_in_diff:
            _, is_new = all_functions_in_diff[func_name]
            if is_new:
                constructs['added'].add(func_name)
            else:
                constructs['modified'].add(func_name)
        else:
            # Function definition might be outside the diff context
            constructs['modified'].add(func_name)
    
    # Build the final result
    constructs['all'] = constructs['added'].union(constructs['modified'])
    
    result = {
        'added': sorted(list(constructs['added'])),
        'modified': sorted(list(constructs['modified'])),
        'all': sorted(list(constructs['all']))
    }
    
    print(f"DEBUG: Summary - Added: {len(result['added'])}, Modified: {len(result['modified'])}, Total: {len(result['all'])}", file=sys.stderr)
    
    return result


def main():
    # Parse command line arguments
    base_ref = "origin/main"
    output_format = "all"  # all, added, modified
    
    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == "--test":
            # Test mode: process a file directly
            if i + 1 < len(sys.argv):
                test_file = sys.argv[i + 1]
                print(f"TEST MODE: Analyzing file {test_file}", file=sys.stderr)
                try:
                    with open(test_file, 'r') as f:
                        content = f.read()
                    # Simulate diff by adding + to each line
                    diff_content = '\n'.join('+' + line for line in content.split('\n'))
                    constructs = extract_changed_verus_constructs(diff_content)
                    if constructs['all']:
                        print(f"TEST MODE: Found {len(constructs['all'])} Verus constructs:", file=sys.stderr)
                        for func in constructs['all']:
                            print(func)
                    else:
                        print("TEST MODE: No Verus constructs found", file=sys.stderr)
                except Exception as e:
                    print(f"TEST MODE ERROR: {e}", file=sys.stderr)
            return 0
        elif arg == "--format":
            if i + 1 < len(sys.argv):
                output_format = sys.argv[i + 1]
                i += 1
        elif not arg.startswith('--'):
            base_ref = arg
        i += 1
    
    print(f"Analyzing git diff against {base_ref}...", file=sys.stderr)
    
    # Get the diff
    diff_output = get_git_diff(base_ref)
    if not diff_output:
        print("No diff output found", file=sys.stderr)
        return 0
    
    # Extract constructs
    constructs = extract_changed_verus_constructs(diff_output)
    
    # Output based on format
    if output_format == "added":
        output_list = constructs['added']
    elif output_format == "modified":
        output_list = constructs['modified']
    else:  # all
        output_list = constructs['all']
    
    if output_list:
        print(f"Found {len(output_list)} Verus constructs ({output_format}):", file=sys.stderr)
        for construct in output_list:
            print(construct)
    else:
        print(f"No Verus constructs found ({output_format})", file=sys.stderr)
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
