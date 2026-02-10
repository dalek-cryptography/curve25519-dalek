#!/usr/bin/env python3
"""
Extract Verus spec functions and verified function contracts for the specs browser.

Outputs JSON with two sections:
  - spec_functions: spec fn definitions (full body)
  - verified_functions: implementation function contracts (signature + requires/ensures only)

Default (hybrid) mode re-extracts live code from .rs source files.

Usage:
    python scripts/extract_specs.py [--output docs/specs_data.json]
    python scripts/extract_specs.py --csv-only [--output docs/specs_data.json]
"""

import argparse
import csv
import json
import os
import re
import sys
from pathlib import Path

GITHUB_BASE = "https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/"

# Regex to match spec fn declarations
SPEC_FN_PATTERN = re.compile(
    r"^(\s*)"
    r"((?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed|uninterp)\s+)*spec\s+fn)\s+"
    r"(\w+)"
)

# Regex to match regular fn declarations (for verified functions)
IMPL_FN_PATTERN = re.compile(r"^(\s*)(?:pub\s+)?fn\s+(\w+)")

# Regex to match proof fn axiom_* declarations
AXIOM_FN_PATTERN = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?proof\s+fn\s+(axiom_\w+)")

FUZZY_LINE_RANGE = 40

DEFAULT_SPEC_CSV = "data/libsignal_verus_specs/generated/spec_functions.csv"
DEFAULT_VERIFIED_CSV = "data/libsignal_verus_specs/generated/verified_functions.csv"
DEFAULT_TRACKED_CSV = "outputs/curve25519_functions.csv"
DEFAULT_FUNCTIONS_TO_TRACK_CSV = "functions_to_track.csv"


# ── Shared helpers ────────────────────────────────────────────────────


def derive_module(filepath: str) -> str:
    """Derive a short module name from a file path.

    Works with both relative paths (curve25519-dalek/src/foo.rs) and
    absolute paths (/home/.../curve25519-dalek/src/foo.rs) by finding the
    ``src`` path segment and building the module path from everything after it.
    """
    parts = Path(filepath).with_suffix("").parts
    if "src" in parts:
        src_idx = parts.index("src")
        rel_parts = parts[src_idx + 1 :]
    else:
        rel_parts = parts
    rel = "::".join(rel_parts)
    if rel.endswith("::mod"):
        rel = rel[: -len("::mod")]
    return rel


def derive_short_module(filepath: str) -> str:
    """Get just the file stem (edwards, scalar, ristretto, montgomery)."""
    return Path(filepath).stem


# Map spec source paths to the same short module names used by verified functions
_SPEC_MODULE_MAP = {
    "edwards_specs": "edwards",
    "montgomery_specs": "montgomery",
    "ristretto_specs": "ristretto",
    "scalar_specs": "scalar",
    "scalar52_specs": "scalar",
    "field_specs": "field",
    "field_specs_u64": "field",
    "core_specs": "core",
}


def derive_category_module(filepath: str) -> str:
    """Map a spec source file to a short category module name.

    This ensures spec functions use the same module names as verified functions
    (e.g. 'edwards' instead of 'specs::edwards_specs') for consistent filtering.
    """
    stem = Path(filepath).stem
    if stem in _SPEC_MODULE_MAP:
        return _SPEC_MODULE_MAP[stem]
    # For lemma files, use a generic 'lemmas' category
    if "lemmas" in filepath:
        return "lemmas"
    return stem


def _short_module_name(full_module: str) -> str:
    """Convert full Rust module path to a short display name.

    Examples:
        curve25519_dalek::montgomery -> montgomery
        curve25519_dalek::backend::serial::u64::scalar -> backend
        curve25519_dalek::scalar_mul::straus -> backend
        curve25519_dalek::backend::serial::curve_models -> backend
    """
    prefix = "curve25519_dalek::"
    short = (
        full_module[len(prefix) :] if full_module.startswith(prefix) else full_module
    )
    # Group internal / backend modules under a single "backend" label:
    #   backend::serial::* (u64::field, u64::scalar, curve_models, ...)
    #   scalar_mul::*
    backend_prefix = "backend::serial::"
    if short.startswith(backend_prefix):
        return "backend"
    if short.startswith("scalar_mul::") or short == "scalar_mul":
        return "backend"
    return short


def _parse_github_link(link: str) -> tuple[str, int]:
    """Extract relative source path and line number from a GitHub link."""
    match = re.search(r"/blob/main/(.+?)#L(\d+)", link)
    if match:
        return match.group(1), int(match.group(2))
    return "", 0


def _parse_function_name(raw: str) -> tuple[str, str, str]:
    """Parse qualified function name into (base_name, display_name, impl_type).

    Examples:
        MontgomeryPoint::ct_eq(&MontgomeryPoint) -> (ct_eq, MontgomeryPoint::ct_eq, MontgomeryPoint)
        elligator_encode(&FieldElement) -> (elligator_encode, elligator_encode, "")
    """
    raw = raw.strip().strip('"')
    paren_idx = raw.find("(")
    before_paren = raw[:paren_idx].strip() if paren_idx != -1 else raw.strip()

    last_sep = before_paren.rfind("::")
    if last_sep != -1:
        impl_type = before_paren[:last_sep]
        base_name = before_paren[last_sep + 2 :]
        display_name = before_paren
    else:
        impl_type = ""
        base_name = before_paren
        display_name = before_paren

    return base_name, display_name, impl_type


def _detect_is_public(contract_text: str) -> bool:
    """Check if a function is truly public from its contract text.

    Returns True for ``pub fn`` / ``pub unsafe fn`` but NOT for
    ``pub(crate)``, ``pub(super)``, or ``pub(in ...)``.
    """
    if not contract_text:
        return False
    stripped = contract_text.lstrip()
    # `pub fn` or `pub unsafe fn` — truly public
    if stripped.startswith("pub "):
        return True
    # `pub(crate)`, `pub(super)`, `pub(in ...)` — NOT truly public
    return False


# ── Auto-generate math interpretation for axioms ──────────────────────

# Words that start a prose line (not a formula line) in doc comments
_PROSE_STARTERS = re.compile(
    r"^(This|The|If|Each|For|Used|Note|See|From|Both|Mathematical|"
    r"Requires|Admitted|In|Without|To|Output|Statistical|"
    r"All|Every|Points|Axiom|AXIOM|Here)",
    re.IGNORECASE,
)


def _extract_math_from_doc(doc_comment: str) -> str:
    """Try to extract a concise formula line from a doc comment.

    Looks for lines containing = or ≡ that look like mathematical formulas
    rather than prose sentences.
    """
    if not doc_comment:
        return ""
    for line in doc_comment.split("\n"):
        line = line.strip()
        if not line:
            continue
        # Must contain an equals/equiv sign
        if "=" not in line and "≡" not in line:
            continue
        # Skip lines that start with prose words
        if _PROSE_STARTERS.match(line):
            continue
        # Skip very long lines (likely prose)
        if len(line) > 100:
            continue
        # Skip lines with many English words (more than 4 non-math words)
        words = re.findall(r"[a-zA-Z]{4,}", line)
        math_symbols = sum(
            1
            for w in words
            if w.lower()
            in {
                "sqrt",
                "mod",
                "sum",
                "prod",
                "lim",
                "inf",
                "prime",
                "identity",
                "basepoint",
                "torsion",
            }
        )
        if len(words) - math_symbols > 4:
            continue
        return line
    return ""


# Symbolic substitution patterns for ensures clause → math notation
_MATH_SUBSTITUTIONS = [
    # Edwards operations
    (
        r"edwards_add\(edwards_neg\((\w+)\)\.0,\s*edwards_neg\((\w+)\)\.1,\s*edwards_neg\((\w+)\)\.0,\s*edwards_neg\((\w+)\)\.1\)",
        r"-\1 + (-\3)",
    ),
    (
        r"edwards_neg\(edwards_add\((\w+)\.0,\s*(\w+)\.1,\s*(\w+)\.0,\s*(\w+)\.1\)\)",
        r"-(\1 + \3)",
    ),
    (
        r"edwards_add\((\w+)\.0,\s*(\w+)\.1,\s*edwards_neg\((\w+)\)\.0,\s*edwards_neg\((\w+)\)\.1\)",
        r"\1 + (-\3)",
    ),
    (r"edwards_add\((\w+)\.0,\s*(\w+)\.1,\s*(\w+)\.0,\s*(\w+)\.1\)", r"\1 + \3"),
    (r"edwards_add\((\w+),\s*(\w+),\s*(\w+),\s*(\w+)\)", r"(\1,\2) + (\3,\4)"),
    (r"edwards_scalar_mul_signed\((\w+),\s*(\w+)\)", r"[\2]\1"),
    (r"edwards_scalar_mul\(edwards_neg\((\w+)\),\s*(\w+)\)", r"[\2](-\1)"),
    (r"edwards_neg\(edwards_scalar_mul\((\w+),\s*(\w+)\)\)", r"-[\2]\1"),
    (r"edwards_scalar_mul\((\w+),\s*(\w+)\)", r"[\2]\1"),
    (r"edwards_neg\((\w+)\)", r"-\1"),
    (r"math_edwards_identity\(\)", "O"),
    # Montgomery operations
    (r"montgomery_add\(montgomery_add\((\w+),\s*(\w+)\),\s*(\w+)\)", r"(\1 + \2) + \3"),
    (r"montgomery_add\((\w+),\s*montgomery_add\((\w+),\s*(\w+)\)\)", r"\1 + (\2 + \3)"),
    (r"montgomery_add\((\w+),\s*montgomery_neg\((\w+)\)\)", r"\1 + (-\2)"),
    (r"montgomery_add\((\w+),\s*(\w+)\)", r"\1 + \2"),
    (r"montgomery_neg\((\w+)\)", r"-\1"),
    (r"MontgomeryAffine::Infinity", "∞"),
    # Field operations
    (r"math_field_mul\((\w+),\s*math_field_inv\((\w+)\)\)", r"\1 / \2"),
    (r"math_field_mul\((\w+),\s*(\w+)\)", r"\1 * \2"),
    (r"math_field_add\((\w+),\s*(\w+)\)", r"\1 + \2"),
    (r"math_field_sub\((\w+),\s*(\w+)\)", r"\1 - \2"),
    (r"math_field_inv\((\w+)\)", r"\1^(-1)"),
    # Other
    (r"is_prime\(p\(\)\)", "p is prime"),
    (r"is_square_mod_p\((\w+)\)", r"\1 is QR mod p"),
    (r"!is_square_mod_p\(([^)]+)\)", r"\1 is not QR mod p"),
    (r"spec_sqrt_m1\(\)", "i"),
    (r"p\(\)\s*-\s*1", "p - 1"),
    (r"p\(\)", "p"),
    (r"pow\(([^,]+),\s*(\w+)\)", r"(\1)^\2"),
    (r"binomial_sum\((\w+),\s*(\w+),\s*(\w+)\)", r"Σ C(\2,k)·\1^k"),
    (r"\bas\s+(?:int|nat)\b", ""),
    (r"\s*==\s*", " = "),
    (r"\s*%\s*", " mod "),
]


# Manual math overrides for axioms whose ensures clauses are too complex
# for automated simplification
_AXIOM_MATH_OVERRIDES = {
    "axiom_hash_is_canonical": "field_element(P1) = field_element(P2) => hash(P1) = hash(P2)",
    "axiom_edwards_d2_is_2d": "D2 = 2*D in F_p",
    "axiom_edwards_add_associative": "(P + Q) + R = P + (Q + R) on Edwards curve",
    "axiom_edwards_scalar_mul_signed_additive": "[a]P + [b]P = [a+b]P (signed scalars)",
    "axiom_xadd_projective_correct": "xADD(U_P:W_P, U_Q:W_Q) represents P + Q",
    "axiom_xdbl_projective_correct": "xDBL(U:W) represents [2]P",
    "axiom_ed25519_basepoint_canonical": "B_x < p, B_y < p",
    "axiom_ed25519_basepoint_table_valid": "ED25519_BASEPOINT_TABLE is valid for B",
    "axiom_eight_torsion_well_formed": "All E[8] torsion points are well-formed",
    "axiom_ristretto_basepoint_table_valid": "RISTRETTO_BASEPOINT_TABLE is valid for Ristretto basepoint",
    "axiom_affine_odd_multiples_of_basepoint_valid": "[1*B, 3*B, ..., 127*B] table is valid",
    "axiom_birational_edwards_montgomery": "(z+y)/(z-y) = (1+y/z)/(1-y/z) (birational map)",
    "axiom_uniform_bytes_split": "split(uniform_64) -> (uniform_32, uniform_32, independent)",
    "axiom_uniform_elligator_sum": "P1 + P2 is uniform if P1, P2 independent from Elligator",
    "axiom_uniform_point_add": "P1 + P2 is uniform if P1, P2 uniform and independent",
    "axiom_uniform_mod_reduction": "X mod L is uniform over Z_L when X uniform over [0, 2^512)",
    "axiom_sqrt_m1_squared": "i^2 = -1 (mod p), where i = sqrt(-1)",
    "axiom_sqrt_m1_not_square": "sqrt(-1) is not a quadratic residue mod p",
    "axiom_neg_sqrt_m1_not_square": "-sqrt(-1) is not a quadratic residue mod p",
    "axiom_p_is_prime": "p = 2^255 - 19 is prime",
    "axiom_sha512_output_length": "|SHA-512(input)| = 64 bytes",
    "axiom_from_bytes_uniform": "uniform bytes => uniform field element",
    "axiom_from_bytes_independent": "independent bytes => independent field elements",
    "axiom_uniform_elligator": "uniform field element => uniform over Elligator image",
    "axiom_uniform_elligator_independent": "independent field elements => independent Ristretto points",
}


# ── Libsignal-used functions ─────────────────────────────────────────
# (base_name, source_file_stem) pairs.  Derived from SCIP call-graph
# analysis of libsignal → curve25519-dalek.  Excludes trait functions
# (is_identity, vartime_multiscalar_mul) and the lizard module.
_LIBSIGNAL_FUNCTIONS: set[tuple[str, str]] = {
    # edwards.rs (8)
    ("as_bytes", "edwards"),
    ("compress", "edwards"),
    ("decompress", "edwards"),
    ("is_small_order", "edwards"),
    ("mul_by_cofactor", "edwards"),
    ("neg", "edwards"),
    ("to_montgomery", "edwards"),
    ("vartime_double_scalar_mul_basepoint", "edwards"),
    # montgomery.rs (1)
    ("to_edwards", "montgomery"),
    # ristretto.rs (17 unique names)
    ("as_bytes", "ristretto"),
    ("compress", "ristretto"),
    ("conditional_select", "ristretto"),
    ("ct_eq", "ristretto"),
    ("decompress", "ristretto"),
    ("default", "ristretto"),
    ("double_and_compress_batch", "ristretto"),
    ("eq", "ristretto"),
    ("from_slice", "ristretto"),
    ("from_uniform_bytes", "ristretto"),
    ("identity", "ristretto"),
    ("mul", "ristretto"),
    ("mul_base", "ristretto"),
    ("multiscalar_mul", "ristretto"),
    ("neg", "ristretto"),
    ("sub", "ristretto"),
    ("to_bytes", "ristretto"),
    # scalar.rs (13 unique names)
    ("as_bytes", "scalar"),
    ("clamp_integer", "scalar"),
    ("ct_eq", "scalar"),
    ("eq", "scalar"),
    ("from", "scalar"),
    ("from_bytes_mod_order", "scalar"),
    ("from_bytes_mod_order_wide", "scalar"),
    ("from_canonical_bytes", "scalar"),
    ("from_hash", "scalar"),
    ("hash_from_bytes", "scalar"),
    ("invert", "scalar"),
    ("neg", "scalar"),
    ("to_bytes", "scalar"),
}


def _is_libsignal(base_name: str, module: str) -> bool:
    """Check if a function is called by libsignal.

    Uses the short module name (e.g. 'edwards', 'scalar') to avoid false
    positives from backend files that share the same file stem (e.g.
    'u64::scalar' vs top-level 'scalar').
    """
    if (base_name, module) in _LIBSIGNAL_FUNCTIONS:
        return True
    # Some dalek-lite functions have _verus suffix; libsignal calls the original
    if base_name.endswith("_verus"):
        if (base_name[:-6], module) in _LIBSIGNAL_FUNCTIONS:
            return True
    return False


def _generate_math_from_ensures(
    ensures_clauses: list[str], contract_text: str = ""
) -> str:
    """Best-effort symbolic substitution on ensures clauses."""
    # Try to extract raw ensures section from contract text (avoids comma-splitting issues)
    text = ""
    if contract_text:
        ensures_match = re.search(
            r"\bensures\b\s*\n?(.*?)(?:\n\s*\{|$)", contract_text, re.DOTALL
        )
        if ensures_match:
            text = ensures_match.group(1).strip()
            # Remove trailing comma
            text = text.rstrip(",").strip()

    if not text and ensures_clauses:
        text = ", ".join(c.rstrip(",") for c in ensures_clauses)

    if not text:
        return ""

    # Strip outer ({ ... })
    text = re.sub(r"^\(\{", "", text)
    text = re.sub(r"\}\)$", "", text)
    text = text.strip()

    for pattern, repl in _MATH_SUBSTITUTIONS:
        text = re.sub(pattern, repl, text)

    # Clean up remaining Rust syntax
    text = re.sub(r"\blet\s+\w+\s*=\s*", "", text)  # remove let bindings
    text = re.sub(r"\{|\}", "", text)  # remove remaining braces
    text = re.sub(r"\s+", " ", text).strip()  # normalize whitespace

    # If the result still looks too Rust-like (many :: or parens), skip
    if text.count("::") > 2 or text.count("(") > 6:
        return ""
    # If result is too long, skip
    if len(text) > 100:
        return ""
    return text


def generate_axiom_math_interpretation(
    fn_name: str, doc_comment: str, ensures_clauses: list[str], contract_text: str = ""
) -> str:
    """Auto-generate a math_interpretation for an axiom.

    Strategy:
      0. Check manual overrides
      1. Try to extract from doc comment (many axioms have concise formulas)
      2. Fall back to symbolic substitution on ensures clause
    """
    # Pass 0: manual override
    if fn_name in _AXIOM_MATH_OVERRIDES:
        return _AXIOM_MATH_OVERRIDES[fn_name]

    # Pass 1: extract from doc comment
    math = _extract_math_from_doc(doc_comment)
    if math:
        return math

    # Pass 2: symbolic substitution
    return _generate_math_from_ensures(ensures_clauses, contract_text)


def extract_doc_comment(lines: list[str], fn_line_idx: int) -> str:
    """Extract /// doc comment lines immediately above a function."""
    doc_lines = []
    i = fn_line_idx - 1
    while i >= 0 and lines[i].strip().startswith("#["):
        i -= 1
    while i >= 0:
        stripped = lines[i].strip()
        if stripped.startswith("///"):
            doc_lines.insert(0, stripped[3:].strip())
            i -= 1
        else:
            break
    return "\n".join(doc_lines) if doc_lines else ""


def extract_function_body(lines: list[str], start_idx: int) -> tuple[str, int]:
    """Extract full function body by tracking brace depth."""
    body_lines = []
    brace_depth = 0
    found_open_brace = False
    i = start_idx
    while i < len(lines):
        line = lines[i]
        body_lines.append(line)
        for ch in line:
            if ch == "{":
                brace_depth += 1
                found_open_brace = True
            elif ch == "}":
                brace_depth -= 1
        if found_open_brace and brace_depth <= 0:
            return "\n".join(body_lines), i
        i += 1
    return "\n".join(body_lines), i - 1


def dedent_body(body: str, indent: str) -> str:
    if not indent:
        return body
    return "\n".join(
        line[len(indent) :] if line.startswith(indent) else line
        for line in body.split("\n")
    )


def extract_signature(
    lines: list[str], start_idx: int, end_idx: int, indent: str
) -> str:
    sig_lines = []
    for si in range(start_idx, min(end_idx + 1, len(lines))):
        sig_line = lines[si]
        if indent and sig_line.startswith(indent):
            sig_line = sig_line[len(indent) :]
        sig_lines.append(sig_line)
        if "{" in lines[si]:
            last = sig_lines[-1]
            sig_lines[-1] = last[: last.index("{")].rstrip()
            break
    return re.sub(r"\s+", " ", " ".join(s.strip() for s in sig_lines)).strip()


# ── Source file cache ─────────────────────────────────────────────────

_file_cache: dict[str, list[str] | None] = {}


def _strip_comments_and_strings(line: str) -> str:
    """Remove // comments and string literals so brace counting is accurate."""
    result = []
    in_string = False
    escape = False
    i = 0
    while i < len(line):
        c = line[i]
        if escape:
            escape = False
            i += 1
            continue
        if c == "\\" and in_string:
            escape = True
            i += 1
            continue
        if c == '"' and not in_string:
            in_string = True
            i += 1
            continue
        if c == '"' and in_string:
            in_string = False
            i += 1
            continue
        if in_string:
            i += 1
            continue
        # Check for // comment
        if c == "/" and i + 1 < len(line) and line[i + 1] == "/":
            break
        result.append(c)
        i += 1
    return "".join(result)


def _read_file_lines(filepath: str) -> list[str] | None:
    if filepath not in _file_cache:
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                _file_cache[filepath] = f.read().split("\n")
        except (IOError, UnicodeDecodeError) as e:
            print(f"  Warning: Could not read {filepath}: {e}", file=sys.stderr)
            _file_cache[filepath] = None
    return _file_cache[filepath]


# ── Spec function extraction (hybrid) ─────────────────────────────────


def find_spec_fn_in_source(filepath: str, fn_name: str, hint_line: int) -> dict | None:
    lines = _read_file_lines(filepath)
    if lines is None:
        return None

    hint_idx = hint_line - 1
    search_start = max(0, hint_idx - FUZZY_LINE_RANGE)
    search_end = min(len(lines), hint_idx + FUZZY_LINE_RANGE)

    for search_range in [(search_start, search_end), (0, len(lines))]:
        for line_idx in range(search_range[0], search_range[1]):
            match = SPEC_FN_PATTERN.match(lines[line_idx])
            if not match or match.group(3) != fn_name:
                continue
            indent = match.group(1)
            qualifier = match.group(2).strip()
            body, end_idx = extract_function_body(lines, line_idx)
            body = dedent_body(body, indent)
            signature = extract_signature(lines, line_idx, end_idx, indent)
            doc_comment = extract_doc_comment(lines, line_idx)
            return {
                "body": body.rstrip(),
                "signature": signature,
                "doc_comment": doc_comment,
                "line": line_idx + 1,
                "visibility": qualifier,
            }
    return None


def extract_spec_functions(csv_path: str) -> list[dict]:
    """Hybrid extraction of spec functions."""
    specs = []
    found = fell_back = 0

    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row.get("spec_function", "").strip()
            source_path = row.get("source_path", "").strip()
            source_line = int(row.get("source_line", 0))
            csv_def = row.get("definition", "").strip().replace("\\n", "\n")
            csv_doc = row.get("doc_comment", "").strip()
            math_interp = row.get("math_interpretation", "").strip()
            informal_interp = row.get("informal_interpretation", "").strip()

            module = derive_module(source_path)
            short_module = derive_category_module(source_path)
            result = find_spec_fn_in_source(source_path, name, source_line)

            if result:
                body = result["body"]
                signature = result["signature"]
                doc_comment = result["doc_comment"] or csv_doc
                actual_line = result["line"]
                visibility = result["visibility"]
                found += 1
            else:
                body = csv_def
                doc_comment = csv_doc
                actual_line = source_line
                first_line = csv_def.split("\n")[0] if csv_def else ""
                signature = (
                    first_line[: first_line.index("{")].rstrip()
                    if "{" in first_line
                    else first_line.rstrip()
                )
                signature = re.sub(r"\s+", " ", signature).strip()
                vis_match = re.match(
                    r"((?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed|uninterp)\s+)*spec\s+fn)",
                    signature,
                )
                visibility = vis_match.group(1).strip() if vis_match else ""
                if csv_def:
                    fell_back += 1
                else:
                    continue

            fn_id = f"{module.replace('::', '__')}__{name}"
            github_link = f"{GITHUB_BASE}{source_path}#L{actual_line}"

            specs.append(
                {
                    "id": fn_id,
                    "name": name,
                    "signature": signature,
                    "body": body,
                    "file": source_path,
                    "line": actual_line,
                    "module": module,
                    "short_module": short_module,
                    "visibility": visibility,
                    "doc_comment": doc_comment,
                    "math_interpretation": math_interp,
                    "informal_interpretation": informal_interp,
                    "github_link": github_link,
                    "category": "spec",
                }
            )

    print(f"  Spec functions: {found} from source, {fell_back} from CSV")
    return specs


# ── Contract extraction for verified functions ────────────────────────


def extract_contract_from_source(
    filepath: str, fn_name: str, hint_line: int
) -> dict | None:
    """
    Find a function near hint_line and extract its contract:
    signature + requires + ensures (everything before the opening { of the body).
    """
    lines = _read_file_lines(filepath)
    if lines is None:
        return None

    hint_idx = hint_line - 1
    search_start = max(0, hint_idx - FUZZY_LINE_RANGE)
    search_end = min(len(lines), hint_idx + FUZZY_LINE_RANGE)

    for search_range in [(search_start, search_end), (0, len(lines))]:
        for line_idx in range(search_range[0], search_range[1]):
            # Match fn declarations -- look for fn {name}(
            # Must handle: pub fn name, fn name, pub fn name(
            stripped = lines[line_idx].strip()
            # Check if this line declares the function we're looking for
            fn_pattern = re.search(
                r"\bfn\s+" + re.escape(fn_name) + r"\s*[\(<]", stripped
            )
            if not fn_pattern:
                # Also try multiline: fn name(\n
                fn_pattern = re.search(
                    r"\bfn\s+" + re.escape(fn_name) + r"\s*\(", stripped
                )
                if not fn_pattern:
                    continue

            # Found the function declaration. Now extract the contract
            # (everything from this line up to the opening { of the body)
            # We track brace depth to handle match { ... } blocks inside contracts.
            contract_lines = []
            indent = lines[line_idx][
                : len(lines[line_idx]) - len(lines[line_idx].lstrip())
            ]
            requires_clauses = []
            ensures_clauses = []
            current_section = None  # "requires" or "ensures"
            current_clause_lines = []
            brace_depth = 0  # Track nested braces (match blocks, etc.)

            i = line_idx
            while i < len(lines):
                raw_line = lines[i]
                # Dedent
                if indent and raw_line.startswith(indent):
                    display_line = raw_line[len(indent) :]
                else:
                    display_line = raw_line

                # Count braces on this line (ignoring string literals and comments)
                line_for_braces = _strip_comments_and_strings(raw_line)
                opens = line_for_braces.count("{")
                closes = line_for_braces.count("}")

                if i > line_idx and brace_depth == 0 and opens > 0:
                    # A { at depth 0 (after the fn declaration) could be:
                    # (a) the function body opening brace, or
                    # (b) a match/if block inside the contract
                    brace_stripped = raw_line.lstrip()
                    # If the line starts with { alone, it's the body
                    if brace_stripped.startswith("{") and not brace_stripped.startswith(
                        "{|"
                    ):
                        # Flush any pending clause
                        if current_clause_lines:
                            clause_text = " ".join(
                                line.strip() for line in current_clause_lines
                            ).strip()
                            if clause_text:
                                if current_section == "requires":
                                    requires_clauses.append(clause_text)
                                elif current_section == "ensures":
                                    ensures_clauses.append(clause_text)
                        break
                    # Otherwise it's an inline { (e.g. "match result {") — enter nested
                    brace_depth += opens - closes
                    contract_lines.append(display_line)
                    current_clause_lines.append(display_line.strip())
                    i += 1
                    continue

                if brace_depth > 0:
                    # Inside a nested brace block (match arms, etc.)
                    brace_depth += opens - closes
                    contract_lines.append(display_line)
                    current_clause_lines.append(display_line.strip())
                    # If we just closed back to depth 0, the match block ended
                    if brace_depth <= 0:
                        brace_depth = 0
                        # Check if the next meaningful line is the body brace
                    i += 1
                    continue

                contract_lines.append(display_line)

                # Track requires/ensures sections
                trimmed = display_line.strip()
                # Strip leading // comments from clause tracking
                clause_line = trimmed
                if clause_line.startswith("//"):
                    clause_line = ""

                if trimmed == "requires" or trimmed.startswith("requires "):
                    # Flush previous clause
                    if current_clause_lines:
                        clause_text = " ".join(
                            line.strip() for line in current_clause_lines
                        ).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    current_section = "requires"
                    current_clause_lines = []
                elif trimmed == "ensures" or trimmed.startswith("ensures "):
                    if current_clause_lines:
                        clause_text = " ".join(
                            line.strip() for line in current_clause_lines
                        ).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                    current_section = "ensures"
                    current_clause_lines = []
                elif current_section and clause_line:
                    # If line ends with comma, it's a clause boundary
                    current_clause_lines.append(clause_line)
                    if clause_line.rstrip().endswith(","):
                        clause_text = " ".join(
                            line.strip() for line in current_clause_lines
                        ).strip()
                        if clause_text and clause_text not in ("requires", "ensures"):
                            if current_section == "requires":
                                requires_clauses.append(clause_text)
                            elif current_section == "ensures":
                                ensures_clauses.append(clause_text)
                        current_clause_lines = []

                i += 1

            contract_text = "\n".join(contract_lines).rstrip()
            doc_comment = extract_doc_comment(lines, line_idx)
            actual_line = line_idx + 1

            return {
                "contract": contract_text,
                "requires": requires_clauses,
                "ensures": ensures_clauses,
                "doc_comment": doc_comment,
                "line": actual_line,
            }

    return None


def extract_verified_functions(csv_path: str, spec_names: set[str]) -> list[dict]:
    """
    Extract verified function contracts from source, guided by CSV.
    Also detects which spec function names appear in the contract.
    """
    verified = []
    found = 0

    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row.get("function_name", "").strip()
            source_path = row.get("source_path", "").strip()
            source_line = int(row.get("source_line", 0))
            impl_type = row.get("impl_type", "").strip()
            math_interp = row.get("math_interpretation", "").strip()
            informal_interp = row.get("informal_interpretation", "").strip()

            module = derive_short_module(source_path)
            result = extract_contract_from_source(source_path, name, source_line)

            if result:
                contract = result["contract"]
                requires = result["requires"]
                ensures = result["ensures"]
                doc_comment = result["doc_comment"]
                actual_line = result["line"]
                found += 1
            else:
                print(
                    f"  Warning: {name} not found in {source_path}:{source_line}",
                    file=sys.stderr,
                )
                contract = f"fn {name}(...)  // contract not found in source"
                requires = []
                ensures = []
                doc_comment = ""
                actual_line = source_line

            # Detect referenced spec functions
            contract_text = (
                contract + " " + " ".join(requires) + " " + " ".join(ensures)
            )
            referenced = sorted(
                [
                    s
                    for s in spec_names
                    if re.search(r"\b" + re.escape(s) + r"\b", contract_text)
                ]
            )

            # Build unique ID: include impl_type to disambiguate (e.g., edwards::compress vs ristretto::compress)
            type_prefix = impl_type.lower().replace("::", "_") if impl_type else module
            fn_id = f"{type_prefix}__{name}"
            github_link = f"{GITHUB_BASE}{source_path}#L{actual_line}"

            # Display name includes the impl type
            display_name = f"{impl_type}::{name}" if impl_type else name

            verified.append(
                {
                    "id": fn_id,
                    "name": name,
                    "display_name": display_name,
                    "impl_type": impl_type,
                    "contract": contract,
                    "requires": requires,
                    "ensures": ensures,
                    "referenced_specs": referenced,
                    "file": source_path,
                    "line": actual_line,
                    "module": module,
                    "doc_comment": doc_comment,
                    "math_interpretation": math_interp,
                    "informal_interpretation": informal_interp,
                    "github_link": github_link,
                    "category": "verified",
                }
            )

    print(f"  Verified functions: {found} contracts extracted from source")
    return verified


# ── All tracked functions extraction ──────────────────────────────────


def extract_all_tracked_functions(
    tracked_csv: str,
    verified_csv: str,
    spec_names: set[str],
    functions_to_track_csv: str = DEFAULT_FUNCTIONS_TO_TRACK_CSV,
) -> list[dict]:
    """Extract contracts for all 223 tracked functions.

    Uses outputs/curve25519_functions.csv for the function list and metadata,
    and verified_functions.csv for hand-curated interpretations where available.
    """
    # 0. Load impl_block info from functions_to_track.csv
    #    to detect trait implementations (effectively public).
    impl_blocks: dict[tuple[str, str], str] = {}
    if os.path.exists(functions_to_track_csv):
        with open(functions_to_track_csv, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                raw = row.get("function", "").strip()
                mod = row.get("module", "").strip()
                impl_block = row.get("impl_block", "").strip()
                impl_blocks[(raw, mod)] = impl_block
        print(
            f"  Loaded {len(impl_blocks)} impl_block entries "
            f"from {functions_to_track_csv}"
        )

    # 1. Load curated interpretations from verified_functions.csv
    interpretations: dict[tuple[str, str, str], dict] = {}
    if os.path.exists(verified_csv):
        with open(verified_csv, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                fn_name = row.get("function_name", "").strip()
                source_path = row.get("source_path", "").strip()
                impl_type_val = row.get("impl_type", "").strip()
                stem = Path(source_path).stem if source_path else ""
                key = (fn_name, stem, impl_type_val)
                interpretations[key] = {
                    "math": row.get("math_interpretation", "").strip(),
                    "informal": row.get("informal_interpretation", "").strip(),
                }
        print(
            f"  Loaded {len(interpretations)} curated interpretations from {verified_csv}"
        )

    # 2. Process all tracked functions
    functions: list[dict] = []
    found = 0

    with open(tracked_csv, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            raw_fn = row["function"].strip()
            module_path = row["module"].strip()
            link = row["link"].strip()
            has_spec_val = row.get("has_spec", "").strip().lower()
            has_proof_val = row.get("has_proof", "").strip().lower()

            # Parse source path and line from GitHub link
            source_path, source_line = _parse_github_link(link)
            if not source_path:
                print(f"  Warning: Could not parse link for {raw_fn}", file=sys.stderr)
                continue

            # Parse function name
            base_name, display_name, impl_type = _parse_function_name(raw_fn)

            # Derive module
            module = _short_module_name(module_path)

            # Extract contract from source
            result = extract_contract_from_source(source_path, base_name, source_line)

            if result:
                contract = result["contract"]
                requires = result["requires"]
                ensures = result["ensures"]
                doc_comment = result["doc_comment"]
                actual_line = result["line"]
                found += 1
            else:
                print(
                    f"  Warning: {base_name} not found near {source_path}:{source_line}",
                    file=sys.stderr,
                )
                contract = f"fn {base_name}(...)  // contract not found in source"
                requires = []
                ensures = []
                doc_comment = ""
                actual_line = source_line

            # Detect public visibility:
            # 1. `pub fn` in source, OR
            # 2. trait impl (impl_block contains " for ") → effectively public
            impl_block = impl_blocks.get((raw_fn, module_path), "")
            is_trait_impl = " for " in impl_block
            is_public = _detect_is_public(contract) or is_trait_impl

            # Detect libsignal usage (use module name to avoid false positives)
            is_libsignal = _is_libsignal(base_name, module)

            # Look up curated interpretations
            stem = Path(source_path).stem if source_path else ""
            interp = interpretations.get((base_name, stem, impl_type))
            # Also try without _verus suffix for verus-renamed functions
            if not interp and base_name.endswith("_verus"):
                interp = interpretations.get((base_name[:-6], stem, impl_type))
            if not interp:
                interp = {}
            math_interp = interp.get("math", "")
            informal_interp = interp.get("informal", "")

            # Detect referenced spec functions
            contract_text = (
                contract + " " + " ".join(requires) + " " + " ".join(ensures)
            )
            referenced = sorted(
                [
                    s
                    for s in spec_names
                    if re.search(r"\b" + re.escape(s) + r"\b", contract_text)
                ]
            )

            # Build ID prefix
            type_prefix = (
                impl_type.lower()
                .replace("::", "_")
                .replace("<", "_")
                .replace(">", "")
                .replace(" ", "")
                if impl_type
                else module
            )

            github_link = link if link else f"{GITHUB_BASE}{source_path}#L{actual_line}"

            functions.append(
                {
                    "name": base_name,
                    "display_name": display_name,
                    "impl_type": impl_type,
                    "contract": contract,
                    "requires": requires,
                    "ensures": ensures,
                    "referenced_specs": referenced,
                    "file": source_path,
                    "line": actual_line,
                    "module": module,
                    "doc_comment": doc_comment,
                    "math_interpretation": math_interp,
                    "informal_interpretation": informal_interp,
                    "github_link": github_link,
                    "category": "tracked",
                    "is_public": is_public,
                    "is_libsignal": is_libsignal,
                    "has_spec": has_spec_val in ("yes", "ext"),
                    "has_proof": has_proof_val == "yes",
                    "_type_prefix": type_prefix,
                }
            )

    # 3. Assign unique IDs, handling duplicates
    base_id_groups: dict[str, list[dict]] = {}
    for fn in functions:
        base_id = f"{fn['_type_prefix']}__{fn['name']}"
        base_id_groups.setdefault(base_id, []).append(fn)

    for base_id, group in base_id_groups.items():
        if len(group) == 1:
            group[0]["id"] = base_id
        else:
            for fn in group:
                fn["id"] = f"{base_id}_L{fn['line']}"

    # Remove temp fields
    for fn in functions:
        del fn["_type_prefix"]

    print(
        f"  Tracked functions: {found}/{len(functions)} contracts extracted from source"
    )

    public_count = sum(1 for f in functions if f["is_public"])
    libsignal_count = sum(1 for f in functions if f["is_libsignal"])
    spec_count = sum(1 for f in functions if f["has_spec"])
    proof_count = sum(1 for f in functions if f["has_proof"])
    print(
        f"  {public_count} public, {libsignal_count} libsignal-used,"
        f" {spec_count} with specs, {proof_count} with proofs"
    )

    return functions


# ── Discover and extract all spec fns from source ─────────────────────


def discover_all_spec_fns(src_dir: str) -> list[dict]:
    """Scan all .rs files and extract every ``spec fn`` with its full body.

    Returns a list of spec function dicts (same shape as extract_spec_functions
    output) for every spec fn found in the source tree.
    """
    results: list[dict] = []
    src = Path(src_dir)
    rs_files = sorted(src.rglob("*.rs"))

    for rs_file in rs_files:
        filepath = str(rs_file)
        lines = _read_file_lines(filepath)
        if lines is None:
            continue

        for line_idx, line_text in enumerate(lines):
            match = SPEC_FN_PATTERN.match(line_text)
            if not match:
                continue

            fn_name = match.group(3)
            indent = match.group(1)
            qualifier = match.group(2).strip()

            body, end_idx = extract_function_body(lines, line_idx)
            body = dedent_body(body, indent)
            signature = extract_signature(lines, line_idx, end_idx, indent)
            doc_comment = extract_doc_comment(lines, line_idx)

            module = derive_module(filepath)
            short_module = derive_category_module(filepath)
            fn_id = f"{module.replace('::', '__')}__{fn_name}"
            github_link = f"{GITHUB_BASE}{filepath}#L{line_idx + 1}"

            results.append(
                {
                    "id": fn_id,
                    "name": fn_name,
                    "signature": signature,
                    "body": body.rstrip(),
                    "file": filepath,
                    "line": line_idx + 1,
                    "module": module,
                    "short_module": short_module,
                    "visibility": qualifier,
                    "doc_comment": doc_comment,
                    "math_interpretation": "",
                    "informal_interpretation": "",
                    "github_link": github_link,
                    "category": "spec",
                }
            )

    return results


# ── Axiom extraction (auto-discovery) ─────────────────────────────────


def extract_axioms(src_dir: str, spec_names: set[str]) -> list[dict]:
    """Walk all .rs files and extract proof fn axiom_* functions."""
    axioms = []
    src_path = Path(src_dir)
    if not src_path.exists():
        print(f"  Warning: source directory {src_dir} not found", file=sys.stderr)
        return axioms

    rs_files = sorted(src_path.rglob("*.rs"))
    print(f"  Scanning {len(rs_files)} .rs files for axiom functions...")

    for rs_file in rs_files:
        filepath = str(rs_file)
        lines = _read_file_lines(filepath)
        if lines is None:
            continue

        for line_idx, line in enumerate(lines):
            match = AXIOM_FN_PATTERN.match(line)
            if not match:
                continue

            fn_name = match.group(1)

            # Extract contract using the existing brace-aware parser
            result = extract_contract_from_source(filepath, fn_name, line_idx + 1)
            if not result:
                print(
                    f"    Warning: could not extract contract for {fn_name} in {filepath}:{line_idx + 1}",
                    file=sys.stderr,
                )
                continue

            doc_comment = result["doc_comment"]
            contract = result["contract"]
            requires = result["requires"]
            ensures = result["ensures"]
            actual_line = result["line"]

            # Derive module info
            module = derive_module(filepath)
            short_module = derive_category_module(filepath)

            # Auto-generate interpretations
            math_interp = generate_axiom_math_interpretation(
                fn_name, doc_comment, ensures, contract
            )
            # Use only the first meaningful line of the doc comment as informal description
            # (the full doc comment is shown separately in the card)
            informal_lines = (
                [line.strip() for line in doc_comment.split("\n") if line.strip()]
                if doc_comment
                else []
            )
            informal_interp = informal_lines[0] if informal_lines else ""

            # Detect referenced spec functions
            contract_text = (
                contract + " " + " ".join(requires) + " " + " ".join(ensures)
            )
            referenced = sorted(
                [
                    s
                    for s in spec_names
                    if re.search(r"\b" + re.escape(s) + r"\b", contract_text)
                ]
            )

            fn_id = f"{module.replace('::', '__')}__{fn_name}"
            github_link = f"{GITHUB_BASE}{filepath}#L{actual_line}"

            axioms.append(
                {
                    "id": fn_id,
                    "name": fn_name,
                    "signature": "",  # will build from contract first line
                    "body": contract,  # axiom cards show the contract (like verified)
                    "file": filepath,
                    "line": actual_line,
                    "module": module,
                    "short_module": short_module,
                    "visibility": "proof fn",
                    "doc_comment": doc_comment,
                    "math_interpretation": math_interp,
                    "informal_interpretation": informal_interp,
                    "github_link": github_link,
                    "category": "axiom",
                    "referenced_specs": referenced,
                }
            )

    # Build signatures from contract first lines
    for ax in axioms:
        contract = ax["body"]
        if contract:
            first_line = contract.split("\n")[0]
            ax["signature"] = re.sub(r"\s+", " ", first_line).strip()

    print(f"  Found {len(axioms)} axiom functions")
    return axioms


# ── Main ──────────────────────────────────────────────────────────────


def main():
    parser = argparse.ArgumentParser(
        description="Extract Verus specs for the browser website"
    )
    parser.add_argument("--output", "-o", default="docs/specs_data.json")
    parser.add_argument("--spec-csv", default=DEFAULT_SPEC_CSV)
    parser.add_argument("--verified-csv", default=DEFAULT_VERIFIED_CSV)
    parser.add_argument("--tracked-csv", default=DEFAULT_TRACKED_CSV)
    parser.add_argument(
        "--csv-only", action="store_true", help="Skip source re-extraction"
    )
    parser.add_argument("--src-dir", default="curve25519-dalek/src")
    args = parser.parse_args()

    # 1. Extract spec functions
    if not os.path.exists(args.spec_csv):
        print(f"Error: {args.spec_csv} not found.", file=sys.stderr)
        sys.exit(1)

    print(f"Extracting spec functions from {args.spec_csv}...")
    spec_functions = extract_spec_functions(args.spec_csv)
    spec_functions.sort(key=lambda s: (s["module"], s["name"]))

    # Discover ALL spec fns from source and merge with curated list.
    # Curated entries keep their math/informal interpretations; newly discovered
    # ones get empty interpretations but still appear in the right panel.
    curated_names = {s["name"] for s in spec_functions}
    print(f"Discovering all spec functions from {args.src_dir}...")
    all_discovered = discover_all_spec_fns(args.src_dir)
    print(f"  Found {len(all_discovered)} spec fn definitions in source")

    # Add discovered specs not already in the curated list
    added = 0
    for spec in all_discovered:
        if spec["name"] not in curated_names:
            spec_functions.append(spec)
            curated_names.add(spec["name"])
            added += 1

    # Auto-generate interpretations for spec functions missing them
    auto_math = 0
    auto_informal = 0
    for spec in spec_functions:
        doc = spec.get("doc_comment", "")
        # Math interpretation: extract formula from doc comment
        if not spec.get("math_interpretation") and doc:
            math = _extract_math_from_doc(doc)
            if math:
                spec["math_interpretation"] = math
                auto_math += 1
        # Informal interpretation: use first meaningful line of doc comment
        if not spec.get("informal_interpretation") and doc:
            for doc_line in doc.split("\n"):
                doc_line = doc_line.strip()
                if doc_line and not doc_line.startswith("#"):
                    spec["informal_interpretation"] = doc_line
                    auto_informal += 1
                    break

    spec_functions.sort(key=lambda s: (s["module"], s["name"]))
    print(f"  Added {added} spec functions from source (total: {len(spec_functions)})")
    print(
        f"  Auto-generated {auto_math} math + {auto_informal} informal interpretations"
    )

    spec_names = {s["name"] for s in spec_functions}

    # Add spec-to-spec cross-references (which other specs does each spec call?)
    print("Computing spec-to-spec cross-references...")
    for spec in spec_functions:
        body_text = spec.get("body", "")
        own_name = spec["name"]
        referenced = sorted(
            [
                s
                for s in spec_names
                if s != own_name and re.search(r"\b" + re.escape(s) + r"\b", body_text)
            ]
        )
        spec["referenced_specs"] = referenced

    spec_refs_total = sum(len(s["referenced_specs"]) for s in spec_functions)
    specs_with_refs = sum(1 for s in spec_functions if s["referenced_specs"])
    print(
        f"  {spec_refs_total} spec-to-spec references across {specs_with_refs} spec functions"
    )

    # 2. Extract all tracked function contracts (223 functions)
    if os.path.exists(args.tracked_csv):
        print(f"\nExtracting all tracked function contracts from {args.tracked_csv}...")
        verified_functions = extract_all_tracked_functions(
            args.tracked_csv, args.verified_csv, spec_names
        )
        verified_functions.sort(key=lambda s: (s["module"], s["display_name"]))
    elif os.path.exists(args.verified_csv):
        print(
            f"\nWarning: {args.tracked_csv} not found, falling back to {args.verified_csv}",
            file=sys.stderr,
        )
        verified_functions = extract_verified_functions(args.verified_csv, spec_names)
        verified_functions.sort(key=lambda s: (s["module"], s["display_name"]))
    else:
        print(
            "Warning: No tracked or verified CSV found, skipping implementation functions.",
            file=sys.stderr,
        )
        verified_functions = []

    # 3. Extract axiom functions (auto-discovered from source)
    print(f"Extracting axiom functions from {args.src_dir}...")
    axiom_functions = extract_axioms(args.src_dir, spec_names)
    axiom_functions.sort(key=lambda a: (a["module"], a["name"]))

    # 4. Filter spec functions to only those reachable from tracked functions.
    #    Compute transitive closure: start from directly referenced specs,
    #    then follow spec-to-spec references.
    direct_refs: set[str] = set()
    for fn in verified_functions:
        direct_refs.update(fn.get("referenced_specs", []))
    # Also include axiom-referenced specs
    for ax in axiom_functions:
        direct_refs.update(ax.get("referenced_specs", []))

    reachable: set[str] = set(direct_refs)
    spec_lookup_by_name = {s["name"]: s for s in spec_functions}
    frontier = set(direct_refs)
    while frontier:
        new_frontier: set[str] = set()
        for name in frontier:
            spec = spec_lookup_by_name.get(name)
            if spec:
                for ref in spec.get("referenced_specs", []):
                    if ref not in reachable:
                        reachable.add(ref)
                        new_frontier.add(ref)
        frontier = new_frontier

    before = len(spec_functions)
    spec_functions = [s for s in spec_functions if s["name"] in reachable]
    print(
        f"\nFiltered spec functions: {before} -> {len(spec_functions)} "
        f"(keeping {len(direct_refs)} directly referenced + "
        f"{len(reachable) - len(direct_refs)} transitively referenced)"
    )

    # Append axioms to spec_functions list so they appear in the right panel
    all_right_panel = spec_functions + axiom_functions

    # Strip fields not used by the frontend to reduce JSON size
    for fn in verified_functions:
        fn.pop("requires", None)
        fn.pop("ensures", None)
    for spec in all_right_panel:
        spec.pop("short_module", None)

    # 5. Output minified JSON (saves ~10% over pretty-printed)
    output = {
        "spec_functions": all_right_panel,
        "verified_functions": verified_functions,
    }

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(output, f, ensure_ascii=False, separators=(",", ":"))

    # Summary
    spec_mods = sorted(set(s["module"] for s in spec_functions))
    print(f"\n{len(spec_functions)} spec functions from {len(spec_mods)} modules")
    print(f"{len(axiom_functions)} axiom functions")
    verified_mods = sorted(set(s["module"] for s in verified_functions))
    print(
        f"{len(verified_functions)} tracked functions from {len(verified_mods)} modules"
    )

    # Show cross-reference stats
    total_refs = sum(len(v["referenced_specs"]) for v in verified_functions)
    unique_refs = set()
    for v in verified_functions:
        unique_refs.update(v["referenced_specs"])
    print(
        f"{total_refs} total spec references, {len(unique_refs)} unique spec functions referenced"
    )

    # Show axiom math interpretation coverage
    axioms_with_math = sum(1 for a in axiom_functions if a["math_interpretation"])
    print(
        f"{axioms_with_math}/{len(axiom_functions)} axioms have auto-generated math interpretations"
    )
    print(f"\nOutput written to {out_path}")


if __name__ == "__main__":
    main()
