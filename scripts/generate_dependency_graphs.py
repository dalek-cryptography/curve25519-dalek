#!/usr/bin/env python3
"""
Script to generate call graphs for Verus functions.
This script coordinates the call graph generation process using the rust-analyzer-test tool.
"""

import json
import subprocess
import sys
import argparse
from pathlib import Path
import os


class CallGraphGenerator:
    def __init__(self, graph_tool_path, scip_file, output_dir, filter_sources=None, include_callees=False, include_callers=False):
        """Initialize the call graph generator."""
        self.graph_tool_path = Path(graph_tool_path)
        self.scip_file = Path(scip_file)
        self.output_dir = Path(output_dir)
        self.filter_sources = filter_sources
        self.include_callees = include_callees
        self.include_callers = include_callers
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Verify tool exists
        if not self.graph_tool_path.exists():
            raise FileNotFoundError(f"Graph generation tool not found: {graph_tool_path}")
        
        # Verify SCIP file exists
        if not self.scip_file.exists():
            raise FileNotFoundError(f"SCIP file not found: {scip_file}")
    
    def generate_call_graph_for_function(self, func_name, symbol_id, depth=5):
        """Generate a call graph for a single function."""
        print(f"Generating graph for function: {func_name}")
        print(f"Using symbol: {symbol_id}")
        
        output_dot = self.output_dir / f"{func_name}_5.dot"
        
        # Build command
        cmd = [
            str(self.graph_tool_path),
            str(self.scip_file),
            str(output_dot),
            symbol_id,
        ]
        
        # Add filter flag if specified
        if self.filter_sources:
            cmd.append(f"--{self.filter_sources}")
        
        # Add include flags if specified
        if self.include_callees:
            cmd.append("--include-callees")
        if self.include_callers:
            cmd.append("--include-callers")
            
        cmd.extend([
            "--depth", str(depth)
        ])
        
        try:
            # Run the graph generation tool
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout
            )
            
            if result.returncode == 0:
                # Check if the generated file has meaningful content
                if output_dot.exists() and output_dot.stat().st_size > 0:
                    # Convert to other formats
                    svg_file = self.output_dir / f"{func_name}_5.svg"
                    png_file = self.output_dir / f"{func_name}_5.png"
                    
                    self._convert_dot_to_svg(output_dot, svg_file)
                    self._convert_dot_to_png(output_dot, png_file)
                    
                    print(f"✓ Successfully generated graph for {func_name}")
                    return True, "success"
                else:
                    print(f"⚠ Empty graph generated for {func_name}")
                    # Clean up empty file
                    if output_dot.exists():
                        output_dot.unlink()
                    return False, "empty"
            else:
                print(f"✗ Failed to generate graph for {func_name}")
                print(f"Error output: {result.stderr}")
                return False, "error"
                
        except subprocess.TimeoutExpired:
            print(f"✗ Timeout generating graph for {func_name}")
            return False, "timeout"
        except Exception as e:
            print(f"✗ Exception generating graph for {func_name}: {e}")
            return False, "exception"
    
    def _convert_dot_to_svg(self, dot_file, svg_file):
        """Convert DOT file to SVG using graphviz."""
        try:
            subprocess.run(
                ["dot", "-Tsvg", str(dot_file), "-o", str(svg_file)],
                check=True,
                capture_output=True
            )
        except subprocess.CalledProcessError as e:
            print(f"Warning: Failed to convert {dot_file} to SVG: {e}")
    
    def _convert_dot_to_png(self, dot_file, png_file):
        """Convert DOT file to PNG using graphviz."""
        try:
            subprocess.run(
                ["dot", "-Tpng", str(dot_file), "-o", str(png_file)],
                check=True,
                capture_output=True
            )
        except subprocess.CalledProcessError as e:
            print(f"Warning: Failed to convert {dot_file} to PNG: {e}")
    
    def generate_graphs_from_mapping(self, mapping_file, depth=5):
        """Generate graphs for all functions in a mapping file."""
        results = {
            'successful': [],
            'failed': [],
            'empty': [],
            'errors': []
        }
        
        # Read mapping file
        try:
            with open(mapping_file, 'r') as f:
                lines = f.readlines()
        except Exception as e:
            print(f"Error reading mapping file: {e}")
            return results
        
        # Process each function
        for line in lines:
            line = line.strip()
            if not line or '|' not in line:
                continue
            
            try:
                func_name, symbol_id = line.split('|', 1)
                func_name = func_name.strip()
                symbol_id = symbol_id.strip()
                
                if func_name and symbol_id:
                    success, reason = self.generate_call_graph_for_function(func_name, symbol_id, depth)
                    
                    if success:
                        results['successful'].append(func_name)
                    elif reason == "empty":
                        results['empty'].append(func_name)
                    else:
                        results['failed'].append((func_name, reason))
                        
            except ValueError as e:
                print(f"Error parsing line '{line}': {e}")
                results['errors'].append(f"Parse error: {line}")
        
        return results
    
    def create_summary_report(self, results, output_file):
        """Create a markdown summary report of the generation results."""
        with open(output_file, 'w') as f:
            f.write("## Call Graph Generation Summary\n\n")
            
            if results['successful']:
                f.write(f"### ✅ Successfully Generated Graphs ({len(results['successful'])})\n\n")
                for func in results['successful']:
                    f.write(f"- {func}\n")
                f.write("\n")
            
            if results['empty']:
                f.write(f"### ⚠️ Empty Graphs ({len(results['empty'])})\n\n")
                for func in results['empty']:
                    f.write(f"- {func} (no dependencies found)\n")
                f.write("\n")
            
            if results['failed']:
                f.write(f"### ❌ Failed to Generate Graphs ({len(results['failed'])})\n\n")
                for func, reason in results['failed']:
                    f.write(f"- {func} ({reason})\n")
                f.write("\n")
            
            if results['errors']:
                f.write(f"### 🚫 Processing Errors ({len(results['errors'])})\n\n")
                for error in results['errors']:
                    f.write(f"- {error}\n")
                f.write("\n")
    
    def list_generated_files(self):
        """List all generated files in the output directory."""
        print("\nGenerated files:")
        for file_path in sorted(self.output_dir.iterdir()):
            size = file_path.stat().st_size
            print(f"  {file_path.name} ({size} bytes)")


def main():
    parser = argparse.ArgumentParser(description='Generate call graphs for Verus functions')
    parser.add_argument('graph_tool', help='Path to generate_function_subgraph_dot binary')
    parser.add_argument('scip_file', help='Path to SCIP JSON file')
    parser.add_argument('mapping_file', help='File with function|symbol mappings')
    parser.add_argument('output_dir', help='Output directory for graphs')
    parser.add_argument('--depth', type=int, default=5, help='Graph depth (default: 5)')
    parser.add_argument('--summary', help='Output file for summary report')
    parser.add_argument('--successful-list', help='Output file for list of successful functions')
    parser.add_argument('--filter-sources', 
                       help='Filter flag to pass to graph tool (e.g., "filter-non-libsignal-sources")')
    parser.add_argument('--include-callees', action='store_true', 
                       help='Include callees in the graph (functions called by the target)')
    parser.add_argument('--include-callers', action='store_true',
                       help='Include callers in the graph (functions that call the target)')
    
    args = parser.parse_args()
    
    try:
        # Create generator
        generator = CallGraphGenerator(args.graph_tool, args.scip_file, args.output_dir, 
                                     args.filter_sources, args.include_callees, args.include_callers)
        
        # Generate graphs
        results = generator.generate_graphs_from_mapping(args.mapping_file, args.depth)
        
        # Create summary report
        if args.summary:
            generator.create_summary_report(results, args.summary)
        
        # Save successful functions list
        if args.successful_list and results['successful']:
            with open(args.successful_list, 'w') as f:
                for func in results['successful']:
                    f.write(f"{func}\n")
        
        # List generated files
        generator.list_generated_files()
        
        # Print summary
        total_attempted = len(results['successful']) + len(results['empty']) + len(results['failed'])
        print(f"\nSummary: {len(results['successful'])} successful, "
              f"{len(results['empty'])} empty, {len(results['failed'])} failed "
              f"out of {total_attempted} functions")
        
        return 0 if results['successful'] else 1
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
