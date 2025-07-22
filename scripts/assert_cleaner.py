#!/usr/bin/env python3
"""
Assert cleaning script - removes lines matching a regex pattern within a specified range.

Usage:
    python assert_cleaner.py <file> <start_line> <end_line> <regex_pattern>

Example:
    python assert_cleaner.py src/main.rs 10 50 "assert.*debug"
"""

import sys
import re
import argparse


def clean_asserts(file_path, start_line, end_line, regex_pattern):
    """
    Remove lines matching regex pattern within the specified line range.
    
    Args:
        file_path: Path to the file to process
        start_line: Starting line number (1-indexed)
        end_line: Ending line number (1-indexed, inclusive)
        regex_pattern: Regex pattern to match lines for removal
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found.", file=sys.stderr)
        return False
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        return False
    
    # Validate line range
    if start_line < 1 or end_line < 1:
        print("Error: Line numbers must be >= 1", file=sys.stderr)
        return False
    
    if start_line > len(lines) or end_line > len(lines):
        print(f"Error: Line range exceeds file length ({len(lines)} lines)", file=sys.stderr)
        return False
    
    if start_line > end_line:
        print("Error: Start line must be <= end line", file=sys.stderr)
        return False
    
    # Compile regex
    try:
        pattern = re.compile(regex_pattern)
    except re.error as e:
        print(f"Error: Invalid regex pattern: {e}", file=sys.stderr)
        return False
    
    # Process lines in the specified range
    removed_count = 0
    new_lines = []
    
    for i, line in enumerate(lines, 1):
        # Check if line is in the specified range
        if start_line <= i <= end_line:
            if pattern.search(line.strip()):
                print(f"Removing line {i}: {line.rstrip()}")
                removed_count += 1
                continue
        
        new_lines.append(line)
    
    # Write back to file if changes were made
    if removed_count > 0:
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(new_lines)
            print(f"Successfully removed {removed_count} lines from {file_path}")
            return True
        except Exception as e:
            print(f"Error writing file: {e}", file=sys.stderr)
            return False
    else:
        print("No matching lines found in the specified range.")
        return True


def main():
    parser = argparse.ArgumentParser(
        description="Remove lines matching a regex pattern within a specified line range",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python assert_cleaner.py src/main.rs 10 50 "assert.*debug"
  python assert_cleaner.py test.py 1 100 "^\\s*assert\\s"
        """
    )
    
    parser.add_argument('file', help='File to process')
    parser.add_argument('start_line', type=int, help='Starting line number (1-indexed)')
    parser.add_argument('end_line', type=int, help='Ending line number (1-indexed, inclusive)')
    parser.add_argument('regex', help='Regex pattern to match lines for removal')
    
    args = parser.parse_args()
    
    success = clean_asserts(args.file, args.start_line, args.end_line, args.regex)
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()