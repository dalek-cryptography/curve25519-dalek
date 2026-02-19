# Lemma reference and search guide

## Where to search (priority order)

1. Same file: helper lemmas nearby are often the right abstraction.
2. Common lemmas: `lemmas/common_lemmas/`
   - `to_nat_lemmas.rs`: byte/nat conversions, little-endian encoding
   - `pow_lemmas.rs`: powers of 2, exponent arithmetic
   - `div_mod_lemmas.rs`: modular arithmetic
   - `bit_lemmas.rs`: bitwise operations
3. Domain folders: `field_lemmas/`, `edwards_lemmas/`, `montgomery_lemmas/`, etc.

## Where to put new helper lemmas

Place lemmas in the module that matches their scope so they stay reusable and avoid circular deps.

| Kind of lemma | Put in | Examples |
|---------------|--------|----------|
| **Generic field algebra** (holds for any d / any field elements) | `lemmas/field_lemmas/field_algebra_lemmas.rs` | From curve eq derive x²·v=u; on-curve (x,y) witnesses valid y; y²=1 ⇒ x=0 when d+1≠0. Take `d` as parameter; precondition = curve equation in field form. No EDWARDS_D or math_on_edwards_curve. |
| **Ed25519 curve structure** (tied to EDWARDS_D or curve predicate) | `lemmas/edwards_lemmas/curve_equation_lemmas.rs` | lemma_unique_x_with_parity, axiom_d_plus_one_nonzero. Call field lemmas with d = EDWARDS_D; don’t duplicate their proofs. |
| **Decompression / Montgomery→Edwards** (spec match, to_edwards correctness) | `lemmas/edwards_lemmas/decompress_lemmas.rs` | lemma_decompress_spec_matches_point, lemma_to_edwards_correctness. Not generic curve eq; about decompress API and birational map. |

**Guidelines:**

- Prefer calling generic field lemmas directly at call sites (e.g. `lemma_field_curve_eq_x2v_eq_u(d, x, y)` with `d = fe51_as_canonical_nat(&EDWARDS_D)`) rather than thin curve-only wrappers. If you keep a wrapper, make it a one-liner that just calls the field lemma.
- Avoid “connection” lemmas whose precondition is exactly another lemma’s postcondition; inline that proof at the single call site instead.
- Lemmas used from another module must be `pub proof fn` (e.g. `axiom_d_plus_one_nonzero` used from decompress_lemmas).

## Search patterns

Common patterns to search for:

- `lemma_u8_32_as_nat_*` (byte array reasoning)
- `lemma_pow2_*` (powers of 2)
- `lemma_mod_*` (modular arithmetic)
- `lemma_*_bound` (bounds)

Command snippets (prefer `rg` if available; fall back to `grep -R`):

```bash
rg "lemma_u8_32_as_nat" curve25519-dalek -g"*.rs"
rg "opaque" curve25519-dalek -g"*.rs"
```

```bash
grep -R --line-number "lemma_u8_32_as_nat" curve25519-dalek --include="*.rs"
grep -R --line-number "opaque" curve25519-dalek --include="*.rs"
```

## Common lemma names (examples)

### Byte-to-nat (`to_nat_lemmas.rs`)

- `lemma_u8_32_as_nat_lower_bound(bytes, index)`: lower bound contribution from a specific byte
- `lemma_u8_32_as_nat_mod_truncates(bytes, n)`: modulo truncates to the first `n` bytes
- `lemma_u8_32_as_nat_equals_rec(bytes)`: connect to recursive definition
- `lemma_decomposition_prefix_rec(bytes, n)`: split into prefix + suffix
- `lemma_prefix_equal_when_bytes_match`: equal prefixes from equal bytes

### Power-of-2 (`pow_lemmas.rs`)

- `lemma_pow2_adds(a, b)`: `pow2(a) * pow2(b) == pow2(a+b)`
- `lemma_pow2_even(n)`: `pow2(n)` is even for `n >= 1`
- `lemma_pow2_pos(n)`: `pow2(n) > 0`
- `lemma2_to64()`: establishes small powers (`2^0` through `2^64`)

### Modular arithmetic (`div_mod_lemmas.rs`)

- `lemma_mod_mod(x, a, b)`: relate `(x % a) % b` to `x % b`
- `lemma_mod_add_multiples_vanish(a, m)`: `(a + m) % m == a % m`
- `lemma_small_mod(x, m)`: if `x < m` then `x % m == x`
- `lemma_mod_bound(x, m)`: `x % m < m`

### Field-specific (`field_specs_u64.rs`)

- `pow255_gt_19()`: proves `pow2(255) > 19`, thus `p() < pow2(255)` in Curve25519 contexts
- `p_gt_2()`: proves `p() > 2`
