# Worked patterns (from “compress” proof work)

## Pattern 1: Prove bit properties from value bounds

```rust
// Goal: Prove (bytes[31] >> 7) == 0
// Given: val < p() where p() < pow2(255)

assert(p() < pow2(255)) by { pow255_gt_19(); };
lemma_bytes32_to_nat_lower_bound(bytes, 31);

assert(bytes[31] < 128) by {
    if bytes[31] >= 128 {
        assert(pow2(7) == 128) by { lemma2_to64(); };
        assert(pow2(7) * pow2(248) == pow2(255)) by { lemma_pow2_adds(7, 248); };
        assert(val >= pow2(255));
        assert(false);
    }
};

assert((bytes[31] >> 7) == 0) by (bit_vector)
    requires bytes[31] < 128;
```

## Pattern 1b: Cache exec calls for proof mode

If a later proof needs to mention the result of an exec-only helper (e.g., `invert()`) and Verus
rejects calling it in a `proof {}` block, compute it once in exec mode:

```rust
let inv = x.invert();
// use `inv` in exec code
let y = &a * &inv;

proof {
    // use postconditions about `inv` / `y` without re-calling `invert()`
}
```

## Pattern 2: Connect byte operations to field values (parity)

```rust
// Goal: Relate (bytes[0] & 1) to field_value % 2

lemma_bytes32_to_nat_of_spec_fe51_to_bytes(fe);
let bytes = seq_to_array_32(spec_fe51_to_bytes(fe));
assert(bytes32_to_nat(&bytes) == field_value);

lemma_bytes32_to_nat_mod_truncates(&bytes, 1);
assert(bytes32_to_nat(&bytes) % pow2(8) == bytes[0]);

assert(pow2(8) % 2 == 0) by { lemma_pow2_even(8); };
assert((bytes32_to_nat(&bytes) % pow2(8)) % 2 == bytes32_to_nat(&bytes) % 2) by {
    lemma_mod_mod(bytes32_to_nat(&bytes) as int, pow2(8) as int, 2);
};

assert((bytes[0] & 1 == 1) == (field_value % 2 == 1)) by (bit_vector);
```

## Pattern 3: Prove XOR preserves value modulo a power of 2

```rust
// Goal: Prove XOR-ing bit 255 does not change value mod pow2(255)

assert(byte_after == byte_before + sign_bit * 128) by (bit_vector)
    requires (byte_before >> 7) == 0, sign_bit == 0 || sign_bit == 1;

assert(pow2(7) == 128) by { lemma2_to64(); };
assert(pow2(7) * pow2(248) == pow2(255)) by { lemma_pow2_adds(7, 248); };

lemma_bytes32_to_nat_equals_rec(s_before);
lemma_bytes32_to_nat_equals_rec(s_after);
lemma_decomposition_prefix_rec(s_before, 31);
lemma_decomposition_prefix_rec(s_after, 31);

assert(bytes32_to_nat(s_after) == bytes32_to_nat(s_before) + sign_bit * pow2(255));

assert(bytes32_to_nat(s_after) % pow2(255) == bytes32_to_nat(s_before) % pow2(255)) by {
    if sign_bit == 1 {
        lemma_mod_add_multiples_vanish(bytes32_to_nat(s_before) as int, pow2(255) as int);
    }
};
```
