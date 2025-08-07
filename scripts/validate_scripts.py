#!/usr/bin/env python3
"""
Validation script to test the functionality of our graph generation scripts.
This script performs basic validation without requiring external dependencies.
"""

import sys
import json
import tempfile
from pathlib import Path

def test_symbol_mapper():
    """Test the symbol mapper functionality."""
    print("Testing symbol mapper...")
    
    # Create a mock SCIP file
    mock_scip = {
        "documents": [
            {
                "symbols": [
                    {"symbol": "rust-analyzer cargo curve25519-dalek 4.1.3 backend/serial/u64/field/impl#[FieldElement51]add()"},
                    {"symbol": "rust-analyzer cargo curve25519-dalek 4.1.3 backend/serial/u64/field/impl#[FieldElement51]mul()"},
                    {"symbol": "rust-analyzer cargo curve25519-dalek 4.1.3 edwards/impl#[EdwardsPoint]compress()"},
                ]
            }
        ]
    }
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(mock_scip, f)
        scip_file = f.name
    
    # Create mock functions file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
        f.write("add\nmul\ncompress\n")
        functions_file = f.name
    
    try:
        # Import and test the symbol mapper
        sys.path.insert(0, str(Path(__file__).parent))
        from map_functions_to_symbols import SymbolMapper
        
        mapper = SymbolMapper(scip_file)
        mapping = mapper.map_functions_to_symbols(['add', 'mul', 'compress'])
        
        print(f"Mapped {len(mapping)} functions:")
        for func, symbol in mapping.items():
            print(f"  {func} -> {symbol}")
        
        assert len(mapping) == 3, f"Expected 3 mappings, got {len(mapping)}"
        print("✓ Symbol mapper test passed")
        
    finally:
        Path(scip_file).unlink()
        Path(functions_file).unlink()

def test_gallery_creator():
    """Test the gallery creator functionality."""
    print("\nTesting gallery creator...")
    
    # Create a temporary directory with mock SVG files
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        
        # Create mock SVG files
        for func_name in ['add', 'mul', 'compress']:
            svg_file = temp_path / f"{func_name}_5.svg"
            svg_file.write_text(f'<svg>Mock SVG for {func_name}</svg>')
            
            # Create corresponding DOT and PNG files
            dot_file = temp_path / f"{func_name}_5.dot"
            dot_file.write_text(f'digraph {{ {func_name} }}')
            
            png_file = temp_path / f"{func_name}_5.png"
            png_file.write_bytes(b'mock png data')
        
        # Test gallery creation
        sys.path.insert(0, str(Path(__file__).parent))
        from create_graph_gallery import create_gallery
        
        output_file = temp_path / "gallery.md"
        result = create_gallery(str(temp_path), str(output_file), "Test Gallery")
        
        assert result == 0, "Gallery creation failed"
        assert output_file.exists(), "Gallery file was not created"
        
        content = output_file.read_text()
        assert "Test Gallery" in content, "Title not found in gallery"
        assert "add" in content, "Function 'add' not found in gallery"
        assert "Total Graphs Generated" in content, "Stats not found in gallery"
        
        print("✓ Gallery creator test passed")

def test_function_detector():
    """Test the function detector functionality."""
    print("\nTesting function detector...")
    
    # Create a mock git diff
    mock_diff = """
diff --git a/src/field.rs b/src/field.rs
index 1234567..abcdefg 100644
--- a/src/field.rs
+++ b/src/field.rs
@@ -10,6 +10,12 @@ impl FieldElement {
     }
 }
 
+verus! {
+    fn new_verified_function(x: u64) -> u64 {
+        x + 1
+    }
+}
+
 impl Display for FieldElement {
     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
         write!(f, "FieldElement({})", self.value)
"""
    
    sys.path.insert(0, str(Path(__file__).parent))
    from find_changed_verus_constructs import extract_changed_verus_constructs
    
    constructs = extract_changed_verus_constructs(mock_diff)
    all_functions = constructs['all']
    
    assert 'new_verified_function' in all_functions, "Function not detected in diff"
    print(f"Detected functions: {all_functions}")
    print("✓ Function detector test passed")

def main():
    """Run all validation tests."""
    print("Running validation tests for graph generation scripts...\n")
    
    try:
        test_symbol_mapper()
        test_gallery_creator()
        test_function_detector()
        
        print("\n🎉 All tests passed! Scripts are working correctly.")
        return 0
        
    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback
        traceback.print_exc()
        return 1

if __name__ == '__main__':
    sys.exit(main())
