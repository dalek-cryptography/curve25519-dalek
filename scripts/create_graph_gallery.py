#!/usr/bin/env python3
"""
Script to create a markdown gallery of generated graphs.
This script creates a comprehensive gallery document with all generated graphs.
"""

import sys
import argparse
from pathlib import Path


def create_gallery(graphs_dir, output_file, title="Verus Function Call Graphs"):
    """Create a markdown gallery of all SVG graphs in the directory."""
    graphs_path = Path(graphs_dir)
    
    if not graphs_path.exists():
        print(f"Error: Directory {graphs_dir} does not exist", file=sys.stderr)
        return 1
    
    # Find all SVG files
    svg_files = list(graphs_path.glob("*.svg"))
    
    if not svg_files:
        print(f"Warning: No SVG files found in {graphs_dir}", file=sys.stderr)
        # Create empty gallery
        svg_files = []
    
    # Sort by function name
    svg_files.sort(key=lambda x: x.stem)
    
    with open(output_file, 'w') as f:
        f.write(f"# {title}\n\n")
        
        if svg_files:
            f.write("This document contains the call graphs for newly verified Verus functions in this PR.\n\n")
            f.write(f"**Total Graphs Generated**: {len(svg_files)}\n\n")
            f.write("## Table of Contents\n\n")
            
            # Create table of contents
            for svg_file in svg_files:
                func_name = svg_file.stem.replace('_5', '')  # Remove _5 suffix
                f.write(f"- [Function: `{func_name}`](#{func_name.lower().replace('_', '-')})\n")
            
            f.write("\n")
            
            # Create individual sections for each graph
            for svg_file in svg_files:
                func_name = svg_file.stem.replace('_5', '')  # Remove _5 suffix
                relative_path = svg_file.name
                
                f.write(f"## Function: `{func_name}`\n\n")
                f.write(f"**Graph File**: `{svg_file.name}`\n\n")
                f.write("This graph shows the dependency relationships between the Verus-verified function ")
                f.write(f"`{func_name}` and libsignal functions, with a depth of 5 levels.\n\n")
                f.write(f"![Call Graph for {func_name}]({relative_path})\n\n")
                
                # Check for corresponding DOT and PNG files
                dot_file = graphs_path / f"{func_name}_5.dot"
                png_file = graphs_path / f"{func_name}_5.png"
                
                f.write("**Available Formats**:\n")
                f.write(f"- 🎨 SVG (vector): `{svg_file.name}`\n")
                if png_file.exists():
                    f.write(f"- 🖼️ PNG (raster): `{png_file.name}`\n")
                if dot_file.exists():
                    f.write(f"- 📄 DOT (source): `{dot_file.name}`\n")
                
                f.write("\n---\n\n")
        else:
            f.write("No call graphs were generated for this PR.\n\n")
            f.write("This could mean:\n")
            f.write("- No newly verified Verus functions were detected\n")
            f.write("- The detected functions don't have paths to libsignal functions\n")
            f.write("- There were errors in the graph generation process\n\n")
        
        # Add footer with metadata
        f.write("## Graph Information\n\n")
        f.write("**Graph Parameters**:\n")
        f.write("- **Depth**: 5 levels of function calls\n")
        f.write("- **Direction**: Include callers (functions that call the target)\n")
        f.write("- **Filtering**: Non-libsignal sources filtered out\n")
        f.write("- **Focus**: Paths from Verus-verified functions to libsignal dependencies\n\n")
        
        f.write("**How to Read the Graphs**:\n")
        f.write("- **Nodes**: Represent functions\n")
        f.write("- **Edges**: Represent call relationships (A → B means A calls B)\n")
        f.write("- **Starting Point**: Your newly verified Verus function\n")
        f.write("- **End Points**: libsignal functions that are ultimately reached\n\n")
        
        f.write("*Generated automatically by the Verus Function Graph workflow*\n")
    
    print(f"Gallery created: {output_file}")
    print(f"Included {len(svg_files)} graphs")
    return 0


def main():
    parser = argparse.ArgumentParser(description='Create a markdown gallery of call graphs')
    parser.add_argument('graphs_dir', help='Directory containing SVG graph files')
    parser.add_argument('output_file', help='Output markdown file')
    parser.add_argument('--title', default="Verus Function Call Graphs",
                       help='Title for the gallery')
    
    args = parser.parse_args()
    
    return create_gallery(args.graphs_dir, args.output_file, args.title)


if __name__ == '__main__':
    sys.exit(main())
