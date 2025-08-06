#!/usr/bin/env python3
"""
Script to map Verus function names to their SCIP symbols.
This script loads SCIP data and finds matching symbols for given function names.
"""

import json
import sys
import argparse
from pathlib import Path


class SymbolMapper:
    def __init__(self, scip_file_path):
        """Initialize with SCIP data."""
        self.symbols = []
        self.load_scip_data(scip_file_path)
    
    def load_scip_data(self, scip_file_path):
        """Load and extract symbols from SCIP JSON file."""
        try:
            with open(scip_file_path, 'r') as f:
                scip_data = json.load(f)
                
            # Extract all symbols for easier searching
            if 'documents' in scip_data:
                for doc in scip_data['documents']:
                    if 'symbols' in doc:
                        for symbol in doc['symbols']:
                            symbol_str = symbol.get('symbol', '')
                            if symbol_str:
                                self.symbols.append(symbol_str)
            
            print(f"Loaded {len(self.symbols)} symbols from SCIP data", file=sys.stderr)
            
        except Exception as e:
            print(f"Error loading SCIP data: {e}", file=sys.stderr)
            raise
    
    def find_symbol_for_function(self, func_name):
        """Find the best matching symbol for a function name."""
        print(f"Searching for function: {func_name}", file=sys.stderr)
        
        # Try multiple search strategies
        matching_symbols = []
        
        # Strategy 1: Look for exact function name in impl context
        for s in self.symbols:
            if func_name in s and ('impl' in s or 'field' in s.lower() or 'curve25519' in s.lower()):
                matching_symbols.append(s)
        
        # Strategy 2: If no matches, try broader search
        if not matching_symbols:
            for s in self.symbols:
                if func_name in s:
                    matching_symbols.append(s)
        
        # Strategy 3: Try with different casing
        if not matching_symbols:
            for s in self.symbols:
                if func_name.lower() in s.lower():
                    matching_symbols.append(s)
        
        if matching_symbols:
            # Prefer symbols with 'impl' or specific project context
            best_match = matching_symbols[0]
            for symbol in matching_symbols:
                if 'impl' in symbol or 'curve25519' in symbol.lower():
                    best_match = symbol
                    break
            
            print(f"Found symbol for {func_name}: {best_match}", file=sys.stderr)
            return best_match
        else:
            print(f"No symbol found for function: {func_name}", file=sys.stderr)
            return None
    
    def map_functions_to_symbols(self, function_names):
        """Map a list of function names to their symbols."""
        mapping = {}
        
        for func_name in function_names:
            symbol = self.find_symbol_for_function(func_name)
            if symbol:
                mapping[func_name] = symbol
        
        return mapping


def main():
    parser = argparse.ArgumentParser(description='Map function names to SCIP symbols')
    parser.add_argument('scip_file', help='Path to SCIP JSON file')
    parser.add_argument('functions_file', help='File containing function names (one per line)')
    parser.add_argument('--output', '-o', help='Output file for mapping (default: stdout)')
    parser.add_argument('--format', choices=['pipe', 'json'], default='pipe',
                       help='Output format: pipe-separated or JSON')
    
    args = parser.parse_args()
    
    # Load function names
    try:
        with open(args.functions_file, 'r') as f:
            functions = [line.strip() for line in f if line.strip()]
    except Exception as e:
        print(f"Error reading functions file: {e}", file=sys.stderr)
        return 1
    
    if not functions:
        print("No functions found in input file", file=sys.stderr)
        return 1
    
    print(f"Functions to search for: {functions}", file=sys.stderr)
    
    # Create mapper and find symbols
    try:
        mapper = SymbolMapper(args.scip_file)
        mapping = mapper.map_functions_to_symbols(functions)
    except Exception as e:
        print(f"Error during symbol mapping: {e}", file=sys.stderr)
        return 1
    
    # Output results
    output_file = open(args.output, 'w') if args.output else sys.stdout
    
    try:
        if args.format == 'json':
            json.dump(mapping, output_file, indent=2)
        else:  # pipe format
            for func, symbol in mapping.items():
                print(f"{func}|{symbol}", file=output_file)
    finally:
        if args.output:
            output_file.close()
    
    print(f"Successfully mapped {len(mapping)} out of {len(functions)} functions", file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
