# Lemma reference and search guide

## Where to search (priority order)

1. Same file: helper lemmas nearby are often the right abstraction.
2. Common lemmas: `lemmas/common_lemmas/`
   - `to_nat_lemmas.rs`: byte/nat conversions, little-endian encoding
   - `pow_lemmas.rs`: powers of 2, exponent arithmetic
   - `div_mod_lemmas.rs`: modular arithmetic
   - `bit_lemmas.rs`: bitwise operations
3. Domain folders: `field_lemmas/`, `edwards_lemmas/`, `montgomery_lemmas/`, etc.

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
