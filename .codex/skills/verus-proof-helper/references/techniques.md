# Proof techniques

## 1) Bit-vector reasoning (`by (bit_vector)`)

Use for:

- shifts/masks (`>>`, `&`, `|`, `^`)
- connecting bit ops to arithmetic facts (e.g., `% 2`)

```rust
assert(byte < 128 ==> (byte >> 7) == 0) by (bit_vector);
assert((byte & 1 == 1) == (byte % 2 == 1)) by (bit_vector);

assert(byte_after == byte_before + (sign_bit << 7)) by (bit_vector)
    requires
        (byte_before >> 7) == 0,
        sign_bit == 0 || sign_bit == 1;
```

## 2) Nonlinear arithmetic (`by (nonlinear_arith)`)

Use for multiplication/division inequalities and transitivity chains.

```rust
assert((byte_after as nat) * pow2(248) >= 128 * pow2(248)) by (nonlinear_arith)
    requires byte_after >= 128;
```

## 3) Decomposition

Use for byte-array / sequence proofs:

- `lemma_decomposition_prefix_rec` to split prefix/suffix
- `lemma_u8_32_as_nat_equals_rec` to connect definitions

## 4) Proof by contradiction

```rust
assert(x < bound) by {
    if x >= bound {
        // derive contradiction using lemmas / bounds
        assert(false);
    }
};
```

## 5) Case analysis

```rust
assert(property) by {
    if condition {
        // true case
    } else {
        // false case
    }
};
```

## 6) `calc!` blocks for equality chains

Use `calc!` to make step-by-step transformations explicit and debuggable.

```rust
calc! {
    (==)
    edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k));
    (==) { /* apply a lemma */ }
    { let half = edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k-1));
      edwards_double(half.0, half.1) };
    (==) { /* use IH */ }
    edwards_scalar_mul(point, a * pow2(k));
}
```

## 7) Induction with `decreases`

```rust
pub proof fn lemma_edwards_scalar_mul_mul_pow2(point: (nat, nat), a: nat, k: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k))
            == edwards_scalar_mul(point, a * pow2(k)),
    decreases k,
{
    if k == 0 {
        assert(pow2(0) == 1) by { lemma2_to64(); }
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        let km1 = (k - 1) as nat;
        lemma_edwards_scalar_mul_mul_pow2(point, a, km1);
        // connect IH to goal via asserts or calc!
    }
}
```

## 8) Compositional reasoning (use postconditions)

Track what helpers guarantee and compose those facts via invariants or small lemmas, instead of re-proving internals.

## 9) Specialized lemmas over general ones

If the general lemma is hard (e.g., full group-law composition), introduce a specialized lemma for your common case (often pow2/doubling), then delete unused general lemmas once the specialized version is sufficient.

## 10) Loop invariants for correctness (not just bounds)

Use invariants to track the mathematical meaning of the loop state and “work done so far”.

```rust
for i in 0..32
    invariant
        0 <= i <= 32,
        edwards_point_as_affine(P) == edwards_scalar_mul(basepoint, pow256(i)),
        forall|j: int|
            #![trigger table.0[j as int]]
            0 <= j < i ==> is_valid_lookup_table_affine_coords(
                table.0[j as int].0,
                edwards_scalar_mul(basepoint, pow256(j as nat)),
                8,
            ),
{
    // ...
}
```

## 11) Strengthen specifications (when needed)

If the proof cannot be completed with the current `requires`/`ensures`, strengthen:

1. Preconditions (most common)
2. Helper postconditions (less common; do only if the helper is under your control)

When changing specs, update all implementations and fix downstream callers.

## 12) Prefer by-value lemma parameters

By-value proof lemma parameters are often easier to call and avoid borrowing friction.

```rust
pub proof fn lemma_foo(x: [i8; 64])
    requires is_valid(&x),
    ensures property(&x),
{ }
```

## 13) Extract common loop-proof logic

If multiple loops share 10–20 lines of proof scaffolding (index math, table selection, reveals), factor it into a helper lemma with a clean contract.

## 14) Avoid SMT blowups (`rlimit`): opaque specs + targeted `reveal`

Use when loop invariants or recursive/quantifier-heavy specs cause `rlimit` timeouts:

- Mark expensive `spec fn` as `#[verifier::opaque]`.
- Keep the opaque predicate in the loop invariant.
- `reveal(...)` only inside small helper lemmas/proof blocks where you need specific conjuncts.

Avoid making *simple* specs opaque; it adds boilerplate and can make SMT harder.
