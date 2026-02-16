# Worked patterns (from “compress” proof work)

## Pattern 1: Prove bit properties from value bounds

```rust
// Goal: Prove (bytes[31] >> 7) == 0
// Given: val < p() where p() < pow2(255)

assert(p() < pow2(255)) by { pow255_gt_19(); };
lemma_u8_32_as_nat_lower_bound(bytes, 31);

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

lemma_u8_32_as_nat_of_spec_fe51_to_bytes(fe);
let bytes = seq_to_array_32(spec_fe51_to_bytes(fe));
assert(u8_32_as_nat(&bytes) == field_value);

lemma_u8_32_as_nat_mod_truncates(&bytes, 1);
assert(u8_32_as_nat(&bytes) % pow2(8) == bytes[0]);

assert(pow2(8) % 2 == 0) by { lemma_pow2_even(8); };
assert((u8_32_as_nat(&bytes) % pow2(8)) % 2 == u8_32_as_nat(&bytes) % 2) by {
    lemma_mod_mod(u8_32_as_nat(&bytes) as int, pow2(8) as int, 2);
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

lemma_u8_32_as_nat_equals_rec(s_before);
lemma_u8_32_as_nat_equals_rec(s_after);
lemma_decomposition_prefix_rec(s_before, 31);
lemma_decomposition_prefix_rec(s_after, 31);

assert(u8_32_as_nat(s_after) == u8_32_as_nat(s_before) + sign_bit * pow2(255));

assert(u8_32_as_nat(s_after) % pow2(255) == u8_32_as_nat(s_before) % pow2(255)) by {
    if sign_bit == 1 {
        lemma_mod_add_multiples_vanish(u8_32_as_nat(s_before) as int, pow2(255) as int);
    }
};
```

## Pattern 4: “Precondition plumbing” for arithmetic traits (bounds + sum bounds)

In this repo, many exec ops (`+`, `-`, `*`, `invert`, `square`, etc.) have *proof-visible*
preconditions like `fe51_limbs_bounded(_, 54)` or `sum_of_limbs_bounded(_, _, u64::MAX)`.
When verification fails, it’s often because those preconditions weren’t established in the
right place.

Minimal pattern:

```rust
proof {
    lemma_fe51_limbs_bounded_weaken(&a, 51, 54);
    lemma_fe51_limbs_bounded_weaken(&b, 51, 54);
    lemma_sum_of_limbs_bounded_from_fe51_bounded(&a, &b, 51);
}
let c = &a + &b;

proof {
    // If you need 54-boundedness for later ops, weaken the postcondition.
    assert(fe51_limbs_bounded(&c, 52));
    lemma_fe51_limbs_bounded_weaken(&c, 52, 54);
}
```

Rule of thumb: establish these right before the exec op that needs them, not “somewhere earlier”.

## Pattern 5: Lift representation-level ensures to struct equality (CT selection / assignment)

When a primitive only ensures limb equality, explicitly lift:
`limbs equality → FieldElement equality → struct equality`.

```rust
let out = MyStruct {
    x: FieldElement::conditional_select(&a.x, &b.x, choice),
    y: FieldElement::conditional_select(&a.y, &b.y, choice),
};

proof {
    assert(!choice_is_true(choice) ==> out.x.limbs == a.x.limbs);
    assert(choice_is_true(choice) ==> out.x.limbs == b.x.limbs);

    if !choice_is_true(choice) {
        lemma_field_element51_eq_from_limbs_eq(out.x, a.x);
        lemma_field_element51_eq_from_limbs_eq(out.y, a.y);
        assert(out == *a);
    } else {
        lemma_field_element51_eq_from_limbs_eq(out.x, b.x);
        lemma_field_element51_eq_from_limbs_eq(out.y, b.y);
        assert(out == *b);
    }
}
```

## Pattern 6: Keep `expect`/`unwrap` in exec code by proving `is_some()`

If production code uses `opt.expect("...")`, prefer *proving* `opt.is_some()` (often by
strengthening the callee’s contract or reusing an existing lemma), rather than refactoring to
a `match` with a “dummy” fallback value.

```rust
let opt = f(...);
proof { assert(opt.is_some()); }
let x = opt.expect("..."); // unchanged exec behavior
```

If the missing fact is truly out-of-scope, isolate it behind a narrow `axiom_...` lemma instead
of sprinkling `assume(...)` at call sites.

## Pattern 7: Bridge `==` branches to spec facts (don’t re-compare bytes)

When you write exec code like:

```rust
let b = x == y;
if b { ... }
```

the proof obligation is usually not “prove `b`”, but “use `b` to derive a spec-level equality”.
If `PartialEq` has an `ensures` relating `b` to a spec predicate (e.g., canonical bytes equality),
use that directly rather than adding an extra explicit `ct_eq_*` call.

Typical structure:

```rust
let b = x == y;
if b {
    proof {
        // From `PartialEq::eq` postcondition:
        //   b == (eq_spec(x, y))   or   b == (spec_bytes(x) == spec_bytes(y))
        assert(b == eq_spec(&x, &y));
        assert(eq_spec(&x, &y));
        // Then lift eq_spec(...) to the semantic equality you need using existing lemmas.
    }
}
```
