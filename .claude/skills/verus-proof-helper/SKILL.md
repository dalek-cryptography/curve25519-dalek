---
name: verus-proof-helper
description: Help complete Verus proofs for cryptographic functions by following proven patterns, leveraging existing lemmas, and avoiding solver rlimit (e.g., opaque specs + targeted reveal).
---

# Verus Proof Helper Skill

## Purpose
Help complete Verus proofs for cryptographic functions by following proven patterns and leveraging existing lemmas from the codebase.

## When to Use
- Completing proofs with `admit()` or `assume(...)` statements that need to be replaced with actual proofs
- Proving properties about byte encodings, field operations, or cryptographic primitives
- Working on curve25519-dalek or similar verified cryptography codebases

## Workflow

### Phase 1: Understand the Proof Goal
1. Read the function signature and postconditions to understand what needs to be proven
2. Identify any `admit()` or `assume(...)` statements that need to be replaced
3. Look for comments explaining the mathematical reasoning
4. Check if there are related lemmas that might already exist

### Phase 2: Search for Existing Lemmas
**Key principle: Never reinvent - always reuse existing lemmas**

Search locations (in priority order):
1. **Same file** - Look for helper lemmas nearby
2. **Common lemmas** - Check `lemmas/common_lemmas/`:
   - `to_nat_lemmas.rs` - Byte/nat conversions, little-endian encoding
   - `pow_lemmas.rs` - Power of 2 properties, exponent arithmetic
   - `div_mod_lemmas.rs` - Modular arithmetic
   - `bit_lemmas.rs` - Bitwise operations
3. **Domain-specific lemmas** - Check relevant domain folder (field_lemmas, edwards_lemmas, etc.)

Common patterns to search for:
- `lemma_bytes32_to_nat_*` - For byte array reasoning
- `lemma_pow2_*` - For power of 2 arithmetic
- `lemma_mod_*` - For modular arithmetic
- `lemma_*_bound` - For establishing bounds

### Phase 3: Incremental Proof Development
**Use the "moving assume(false)" technique:**

1. Start with structure, add `assume(false)` at key points:
   ```rust
   proof fn my_lemma() {
       // Step 1: Establish context
       lemma_setup();
       assume(false);

       // Step 2: Main proof
       assert(intermediate_fact);
       assume(false);

       // Step 3: Conclusion
       assert(final_result);
   }
   ```

2. Verify after each step to ensure structure is sound
3. Replace `assume(false)` one at a time, verifying after each replacement
4. Keep intermediate assertions that help the prover

### Phase 4: Apply Proof Techniques

#### Technique 1: Bit Vector Reasoning
Use `by (bit_vector)` for:
- Bitwise operations (XOR, AND, OR, shifts)
- Converting between bit operations and arithmetic
- Proving inequalities involving bit masks

```rust
assert(byte < 128 ==> (byte >> 7) == 0) by (bit_vector);
assert((byte & 1 == 1) == (byte % 2 == 1)) by (bit_vector);
assert(byte_after == byte_before + (sign_bit << 7)) by (bit_vector)
    requires (byte_before >> 7) == 0, sign_bit == 0 || sign_bit == 1;
```

#### Technique 2: Nonlinear Arithmetic
Use `by (nonlinear_arith)` for:
- Multiplication/division inequalities
- Combining multiple arithmetic facts
- Transitivity chains

```rust
assert((byte_after as nat) * pow2(248) >= 128 * pow2(248)) by (nonlinear_arith)
    requires byte_after >= 128;
```

#### Technique 3: Decomposition
For complex structures, decompose into parts:
- Use `lemma_decomposition_prefix_rec` to split byte arrays
- Use `lemma_bytes32_to_nat_equals_rec` to connect definitions
- Prove properties about parts, then combine

#### Technique 4: Proof by Contradiction
When proving `x < bound`:
```rust
assert(x < bound) by {
    if x >= bound {
        // Derive contradiction using lemmas
        assert(false);
    }
};
```

#### Technique 5: Case Analysis
For conditional properties:
```rust
assert(property) by {
    if condition {
        // Prove for true case
    } else {
        // Prove for false case
    }
};
```

#### Technique 6: calc! Blocks for Equality Chains

Use `calc!` blocks to prove equalities through step-by-step transformations:
```rust
calc! {
    (==)
    edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k));
    (==) { /* Apply lemma_edwards_scalar_mul_pow2_succ */ }
    { let half = edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k-1));
      edwards_double(half.0, half.1) };
    (==) { /* Apply inductive hypothesis */ }
    { let half = edwards_scalar_mul(point, a * pow2(k-1));
      edwards_double(half.0, half.1) };
    (==) { /* Use pow2(k) = 2 * pow2(k-1) and distributivity */ }
    edwards_scalar_mul(point, a * pow2(k));
}
```

**When to use:**
- Proving equality through multiple transformations
- Each step applies a different lemma or definition
- Makes the proof structure explicit and easier to verify

**Benefits:**
- Clear logical flow
- Each step can reference specific lemmas in comments
- Easier to debug than nested assertions

#### Technique 7: Inductive Proofs with decreases
For recursive properties, use induction with `decreases` clause:
```rust
pub proof fn lemma_edwards_scalar_mul_mul_pow2(point: (nat, nat), a: nat, k: nat)
    ensures
        edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k))
            == edwards_scalar_mul(point, a * pow2(k)),
    decreases k,
{
    if k == 0 {
        // Base case: prove for k=0
        assert(pow2(0) == 1) by { lemma2_to64(); }
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        // Inductive step
        let km1 = (k - 1) as nat;
        lemma_edwards_scalar_mul_mul_pow2(point, a, km1);  // Apply IH

        // Use calc! block or assertions to connect IH to goal
        calc! {
            (==)
            edwards_scalar_mul(edwards_scalar_mul(point, a), pow2(k));
            // ... steps using IH ...
            (==)
            edwards_scalar_mul(point, a * pow2(k));
        }
    }
}
```

**Key elements:**
- `decreases k` - Tells Verus the recursion terminates
- Base case (k=0 or similar) - Often needs reveals
- Inductive hypothesis - Call the lemma recursively with smaller parameter
- Connecting step - Show how IH implies the goal for k

**Common base cases:**
- For natural numbers: `n == 0`
- For sequences: `s.len() == 0`
- May need `reveal_with_fuel` to unfold recursive definitions

#### Technique 8: Compositional Reasoning
Build proofs by composing proven postconditions of functions:

```rust
// Function with proven postcondition
fn mul_by_pow_2(self, k: u64) -> EdwardsPoint
    ensures
        edwards_point_as_affine(result) == edwards_scalar_mul(
            edwards_point_as_affine(self),
            pow2(k)
        )

// In proof, use the postcondition
for i in 0..32
    invariant
        edwards_point_as_affine(P) == edwards_scalar_mul(basepoint, pow256(i)),
{
    P = P.mul_by_pow_2(8);  // Postcondition gives: new_P = edwards_scalar_mul(old_P, pow2(8))

    proof {
        // Connect: old_P = scalar_mul(base, pow256(i))
        //          new_P = scalar_mul(old_P, pow2(8))
        // Prove:   new_P = scalar_mul(base, pow256(i) * pow2(8))
        //                = scalar_mul(base, pow256(i+1))

        lemma_edwards_scalar_mul_mul_pow2(basepoint, pow256(i), 8);
        assert(pow256(i+1) == pow256(i) * pow2(8)) by {
            vstd::arithmetic::power2::lemma_pow2_adds(8 * i, 8);
        }
    }
}
```

**Strategy:**
1. Identify what each function guarantees in its postcondition
2. Track these properties through loop invariants or assertions
3. Use composition lemmas to connect nested operations
4. Trust the proven postconditions - don't reprove them

**Benefits:**
- Leverages existing verification work
- Cleaner proofs focused on high-level reasoning
- Reduces proof complexity

#### Technique 9: Specialized Lemmas
When a general lemma is hard to prove, create specialized versions for common cases:

**Example: General composition (hard)**
```rust
// This may require complex group law reasoning
proof fn lemma_scalar_mul_composition(point: (nat, nat), a: nat, b: nat)
    ensures scalar_mul(scalar_mul(point, a), b) == scalar_mul(point, a * b)
    // General case: may need associativity, distributivity of group operations
```

**Specialized power-of-2 version (easier)**
```rust
// Power-of-2 case uses doubling, which is simpler
proof fn lemma_scalar_mul_mul_pow2(point: (nat, nat), a: nat, k: nat)
    ensures scalar_mul(scalar_mul(point, a), pow2(k)) == scalar_mul(point, a * pow2(k))
    decreases k,
{
    // Base case and induction over k
    // Uses doubling lemmas which are already proven
}
```

**When to use:**
- General proof requires axioms or complex reasoning
- Specialized case is sufficient for your use case
- Specialized proof uses simpler, already-proven lemmas

**Example from create proof:**
- Needed: composition of scalar multiplications
- General case: requires group law associativity (complex)
- Specialized: only need power-of-2 multipliers
- Result: Clean proof using doubling lemmas

**Cleanup guidance:**
Once you have a working specialized lemma, check if the general lemma is actually used:
```bash
grep -r "lemma_edwards_scalar_mul_composition" --include="*.rs" | grep -v "_pow2"
```
If the general lemma is only called recursively within itself (and by helper lemmas like
`lemma_edwards_scalar_mul_additive`), it can be removed along with its dependencies.
This reduces code size and removes lemmas that rely on admitted axioms.

#### Technique 10: Loop Invariants for Correctness
Beyond bounds, track correctness properties in loop invariants:

```rust
for i in 0..32
    invariant
        // Bounds invariant (traditional)
        0 <= i <= 32,

        // Iterator state invariant
        edwards_point_as_affine(P) == edwards_scalar_mul(basepoint, pow256(i)),

        // Accumulated correctness invariant
        forall|j: int|
            #![trigger table.0[j as int]]
            0 <= j < i ==> is_valid_lookup_table_affine_coords(
                table.0[j as int].0,
                edwards_scalar_mul(basepoint, pow256(j as nat)),
                8,
            ),
{
    // Iteration i creates table[i]
    table.0[i] = create_lookup_table(&P);

    proof {
        // Prove: table[i] is correct for current P
        // Invariant: P equals expected value
        // Therefore: table[i] satisfies spec
    }

    // Update P for next iteration
    P = next_value(P);
}
```

**Key patterns:**
- **Iterator state**: Track what the loop variable represents mathematically
- **Accumulated work**: Use `forall|j| 0 <= j < i ==> property(j)` to track completed iterations
- **Trigger annotations**: `#![trigger array[j]]` helps Verus apply the invariant

**Benefits:**
- Proves functional correctness, not just memory safety
- Final postcondition follows directly from invariant when loop exits
- Makes proof obligations explicit at each iteration

#### Technique 11: Strengthening Specifications
When a proof cannot be completed with current specifications, strengthen them:

**When to use:**
- Proof requires properties not guaranteed by current preconditions
- Individual bounds are insufficient; need composite predicates (e.g., `is_well_formed_edwards_point`)
- Inner function postconditions don't provide enough information for the caller's proof

**Types of strengthening:**
1. **Preconditions:** Require more from callers to enable the proof
2. **Postconditions of used functions:** Strengthen what helper functions guarantee (less common, but sometimes necessary when their postconditions don't expose enough information)

**Example: Strengthening a precondition**
```rust
// BEFORE: Individual bounds insufficient for proof
open spec fn neg_req(self) -> bool {
    fe51_limbs_bounded(&self.X, 52) && fe51_limbs_bounded(&self.T, 52)
}

// AFTER: Composite predicate provides validity + bounds + sum bounded
open spec fn neg_req(self) -> bool {
    // Strengthened: require well-formed point (validity + bounds + sum bounded)
    // This enables proving all postconditions without assumes
    is_well_formed_edwards_point(*self)
}
```

**Implementation checklist:**
1. Identify what additional properties the proof needs
2. Find or create a predicate that provides those properties
3. Update the spec function (e.g., `neg_req`, or the postcondition of a helper)
4. Update ALL implementations that use this spec:
   - Reference implementations (`&self`)
   - Owned implementations (`self`)
   - Trait implementations (e.g., `NegSpecImpl for EdwardsPoint`)
5. Fix any broken proofs caused by the specification change
6. Document why strengthening was necessary

**Handling broken proofs:** Strengthening specifications (preconditions or postconditions) may cause verification failures in callers or downstream proofs. When this happens:
- Fix the broken proofs to satisfy the new specification
- This may require strengthening their specifications as well (propagating changes)
- If a caller cannot reasonably satisfy the stronger precondition, reconsider whether strengthening is the right approach

**Key insight:** It's acceptable to strengthen specifications when:
- The stronger precondition is reasonable for callers
- It enables completing the proof without admits/assumes
- The change is documented for future maintainers

#### Technique 12: By-Value Lemma Parameters
Prefer by-value parameters over references for proof lemmas:

```rust
// BEFORE (by-reference):
pub proof fn lemma_foo(x: &[i8; 64])
    requires is_valid(&x),
    ensures property(&x),

// AFTER (by-value):
pub proof fn lemma_foo(x: [i8; 64])
    requires is_valid(&x),
    ensures property(&x),
```

**Benefits:**
- Cleaner call sites: `lemma_foo(arr)` instead of `lemma_foo(&arr)`
- No borrowing concerns in proof contexts
- Spec functions that take references still work: just add `&` in requires/ensures

**Note:** The requires/ensures may still use `&x` if the underlying spec functions expect references.

#### Technique 13: Extract Common Loop Proof Logic
When two loops have similar proof structure, create a helper lemma:

```rust
// BEFORE: Duplicated in loop1 and loop2
let table_idx = (i / 2) as int;
let table_base = edwards_scalar_mul(B, pow256(table_idx as nat));
assert(0 <= table_idx < 32);
assert(is_valid_lookup_table_affine_coords(tables[table_idx].0, table_base, 8))
    by { reveal(is_valid_edwards_basepoint_table); }
lemma_select_is_signed_scalar_mul(tables[table_idx].0, a[i], selected, table_base);

// AFTER: Single helper lemma
pub proof fn lemma_basepoint_table_select(table: EdwardsBasepointTable, a: Seq<i8>, i: int, selected: AffineNielsPoint, B: (nat, nat))
    requires
        is_valid_edwards_basepoint_table(table, B),
        0 <= i < 64,
        -8 <= a[i] <= 8,
        // select postconditions...
    ensures
        affine_niels_point_as_affine_edwards(selected) == edwards_scalar_mul_signed(
            edwards_scalar_mul(B, pow256((i / 2) as nat)),
            a[i] as int,
        ),

// In loops: single call replaces ~15 lines
lemma_basepoint_table_select(*self, a@, i as int, selected, B);
```

#### Technique 14: Remove Trivial Wrapper Specs
If a spec function is just a wrapper around another with fixed arguments, consider removing it:

```rust
// BEFORE: Trivial wrapper
pub open spec fn radix16_sum(digits: Seq<i8>, B: (nat, nat)) -> (nat, nat) {
    pippenger_partial(digits, 64, B)
}
pub proof fn lemma_radix16_sum_correct(...) { ... }

// AFTER: Use underlying function directly
// - Remove radix16_sum spec
// - Rename lemma_radix16_sum_correct -> lemma_pippenger_sum_correct
// - Update ensures to use pippenger_partial(digits, 64, B)
// - Update all call sites
```

**When to remove:**
- Wrapper adds no semantic value (just fixes a parameter)
- Wrapper name doesn't add clarity over the underlying function
- Simplifies the API without losing expressiveness

**When to keep:**
- Wrapper provides meaningful abstraction (e.g., named algorithm step)
- Multiple lemmas are named around the wrapper concept
- Wrapper is part of the public API

### Phase 5: Handle Common Issues

#### Issue: "Expected Interp(Array), got Interp(FreeVar)"
**Solution:** Extract array elements to local variables before proof blocks
```rust
let byte31 = bytes[31];  // Extract before proof block
proof {
    assert(byte31 < 128);  // Use local variable
}
```

#### Issue: "Cannot call function with mode exec"
**Solution:** Call exec functions outside proof blocks, save results
```rust
let result = exec_function();  // Outside proof block
proof {
    // Use result here
}
```

#### Issue: "Nested proof blocks not supported"
**Solution:** Flatten proof structure
```rust
// Bad:
proof {
    proof { ... }  // Nested!
}

// Good:
let value = exec_call();
proof {
    // Use value
}
```

#### Issue: "Assertion failed" without details
**Solution:** Add intermediate assertions to narrow down the problem
```rust
// Instead of:
assert(complex_property);

// Do:
assert(intermediate_step_1);
assert(intermediate_step_2);
assert(intermediate_step_3);
assert(complex_property);
```

#### Issue: "unresolved import" for vstd items in regular cargo build
**Solution:** Guard ghost-only imports with `#[cfg(verus_keep_ghost)]`
```rust
// Bad: fails clippy/cargo test because vstd isn't available in regular builds
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_adds, pow2};

// Good: only included when running Verus verification
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_adds, pow2};
```
This applies to any imports from `vstd::` or ghost-only modules that aren't available during regular Rust compilation.

#### Issue: "unresolved import" for specific common_lemmas items (cargo test/clippy)
**Cause:** Many `common_lemmas::*` items live inside `verus!` blocks and are not present in non-Verus builds.
**Solution:** Prefer wildcard imports from the module, which compile even when the module is empty.
```rust
// Bad: fails in non-Verus builds if the item isn't generated
use crate::lemmas::common_lemmas::div_mod_lemmas::lemma_int_nat_mod_equiv;

// Good: wildcard import is accepted even if the module has no items
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
```
Use `#[allow(unused_imports)]` to keep clippy clean when the item is only used in proof blocks.

#### Issue: Redundant imports inside proof blocks
**Solution:** Use top-level wildcard imports and short names in proof blocks

When the file has top-level wildcard imports like:
```rust
use crate::lemmas::field_lemmas::add_lemmas::*;
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
use crate::specs::edwards_specs::*;
```

Do NOT add redundant specific imports inside proof blocks:
```rust
// Bad: redundant import already covered by wildcard
proof {
    use crate::lemmas::edwards_lemmas::curve_equation_lemmas::lemma_edwards_add_identity_left;
    lemma_edwards_add_identity_left(x, y);
}

// Good: just use the short name directly
proof {
    lemma_edwards_add_identity_left(x, y);
}
```

**When cleaning up:** Check top-level imports for wildcards (`*`) and remove any specific imports inside proof blocks that are already covered.

### Phase 6: Verification and Cleanup

1. **Verify incrementally:**
   ```bash
   cargo verus verify -- --verify-only-module module_name --verify-function function_name
   ```

2. **Verify integration:**
   ```bash
   cargo verus verify -- --verify-module module_name
   ```

3. **Clean up:**
   - Remove redundant assertions (test by removing one at a time)
   - Add comments explaining non-obvious steps
   - Ensure proof follows codebase style

4. **Simplify assert..by blocks:**
   `assert .. by` blocks should only be used when the `by` part contains **actual lemma calls**.
   If the `by` block only contains simple arithmetic that Z3 can infer directly, remove the `by` part:
   ```rust
   // BEFORE (redundant):
   assert(np1 >= 3) by { assert(n >= 2); };
   assert(mm1 >= 1) by { assert(m >= 2); };
   assert(suf_idx + 2 < digits.len()) by { assert(digits.len() >= 2 * n); };

   // AFTER (simplified):
   assert(np1 >= 3);
   assert(mm1 >= 1);
   assert(suf_idx + 2 < digits.len());
   ```

   Keep `assert .. by` when it contains lemma calls:
   ```rust
   // KEEP: contains actual lemma call
   assert(pow2(k + 1) != 0) by {
       lemma_pow2_pos(k + 1);
       lemma2_to64();
   };
   ```

5. **Move lemma calls into the assert..by blocks they justify:**
   Each lemma should be placed in the `by` block of the assertion it proves. This makes the proof structure explicit about which lemma proves which fact:
   ```rust
   // BEFORE (unclear which lemma proves what):
   lemma_mul_is_associative(b, d, p);
   lemma_mul_is_commutative(b, d);
   lemma_mul_is_associative(d, b, p);
   assert(b * (d * p) == (b * d) * p);
   assert(b * d == d * b);
   assert((d * b) * p == d * (b * p));

   // AFTER (each lemma paired with its assertion):
   assert(b * (d * p) == (b * d) * p) by { lemma_mul_is_associative(b, d, p); }
   assert(b * d == d * b) by { lemma_mul_is_commutative(b, d); }
   assert((d * b) * p == d * (b * p)) by { lemma_mul_is_associative(d, b, p); }
   ```

   **Benefits:**
   - Clear logical structure: you see exactly what each lemma proves
   - Easier to debug: if an assertion fails, you know which lemma isn't working
   - Self-documenting: the proof reads as a series of justified claims

6. **Remove unused lemmas:**
   - Check if general lemmas are actually used outside their own recursive calls
   - If a specialized lemma (e.g., `_pow2` variant) exists with a complete proof, the general
     version may be removable
   - Use grep to check usage: `grep -r "lemma_name" --include="*.rs"`
   - Remove lemmas that are only used by other unused lemmas (transitive cleanup)

7. **Keep comments informative but concise:**
   Proof comments should explain *why*, not restate *what* the code does. Avoid verbose step-by-step explanations that mirror the assertions.

   ```rust
   // BAD: verbose, restates the code
   proof {
       // Step 1: pow256(0) == 1, so the table base for index 0 is just B
       assert(pow256(0) == 1) by { ... }
       // Step 2: edwards_scalar_mul(B, 1) == B
       assert(edwards_scalar_mul(B, 1) == B) by { ... }
       // Step 3: From table validity, table[0] is valid for edwards_scalar_mul(B, pow256(0)) = B
       // The spec says: for j in 0..8, affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(base, j+1)
       // Since select(1) with x=1 > 0 returns self.0[0].0[(1-1)] = self.0[0].0[0]
       assert(is_valid_lookup_table_affine_coords(...));
   }

   // GOOD: concise, explains key insights
   proof {
       assert(pow256(0) == 1) by { ... }
       assert(edwards_scalar_mul(B, 1) == B) by { ... }

       // Table validity: table[0] contains multiples of B
       assert(is_valid_lookup_table_affine_coords((*self).0[0int].0, B, 8));
   }
   ```

   **Guidelines:**
   - One comment per logical block, not per assertion
   - Comment on non-obvious reasoning (e.g., "B is canonical, so B % p == B")
   - Skip comments when the assertion is self-explanatory
   - Don't duplicate information from spec function names or postcondition comments
   - Remove "from X postcondition" comments - the `assert...by` structure makes this clear

## Key Patterns from compress Proof

### Pattern 1: Proving Bit Properties from Value Bounds
```rust
// Goal: Prove (bytes[31] >> 7) == 0
// Given: val < p() where p() < pow2(255)

// Step 1: Establish val < pow2(255)
assert(p() < pow2(255)) by { pow255_gt_19(); };

// Step 2: Get lower bound on bytes32_to_nat
lemma_bytes32_to_nat_lower_bound(bytes, 31);

// Step 3: Contradiction if high bit set
assert(bytes[31] < 128) by {
    if bytes[31] >= 128 {
        assert(pow2(7) == 128) by { lemma2_to64(); };
        assert(pow2(7) * pow2(248) == pow2(255)) by { lemma_pow2_adds(7, 248); };
        assert(val >= pow2(255));  // Contradiction
        assert(false);
    }
};

// Step 4: Bit property follows
assert((bytes[31] >> 7) == 0) by (bit_vector)
    requires bytes[31] < 128;
```

### Pattern 2: Connecting Byte Operations to Field Values
```rust
// Goal: Prove (bytes[0] & 1) relates to field_value % 2


// Step 1: Connect bytes to field value
lemma_bytes32_to_nat_of_spec_fe51_to_bytes(fe);
let bytes = seq_to_array_32(spec_fe51_to_bytes(fe));
assert(bytes32_to_nat(&bytes) == field_value);

// Step 2: Extract first byte using modulo
lemma_bytes32_to_nat_mod_truncates(&bytes, 1);
assert(bytes32_to_nat(&bytes) % pow2(8) == bytes[0]);

// Step 3: Show even modulus preserves parity
assert(pow2(8) % 2 == 0) by { lemma_pow2_even(8); };
assert((bytes32_to_nat(&bytes) % pow2(8)) % 2 == bytes32_to_nat(&bytes) % 2) by {
    lemma_mod_mod(bytes32_to_nat(&bytes) as int, pow2(8) as int, 2);
};

// Step 4: Connect to bit operation
assert((bytes[0] & 1 == 1) == (field_value % 2 == 1)) by (bit_vector);
```

### Pattern 3: Proving XOR Preserves Values Through Modulo
```rust
// Goal: Prove XOR-ing bit 255 doesn't change value mod pow2(255)

// Step 1: Show XOR acts as addition when target bit is 0
assert(byte_after == byte_before + sign_bit * 128) by (bit_vector)
    requires (byte_before >> 7) == 0, sign_bit == 0 || sign_bit == 1;

// Step 2: Establish power relationships
assert(pow2(7) == 128) by { lemma2_to64(); };
assert(pow2(7) * pow2(248) == pow2(255)) by { lemma_pow2_adds(7, 248); };

// Step 3: Decompose bytes32_to_nat to isolate changed byte
lemma_bytes32_to_nat_equals_rec(s_before);
lemma_bytes32_to_nat_equals_rec(s_after);
lemma_decomposition_prefix_rec(s_before, 31);
lemma_decomposition_prefix_rec(s_after, 31);

// Step 4: Compute the difference
assert(bytes32_to_nat(s_after) == bytes32_to_nat(s_before) + sign_bit * pow2(255));

// Step 5: Show modulo removes the added term
assert(bytes32_to_nat(s_after) % pow2(255) == bytes32_to_nat(s_before) % pow2(255)) by {
    if sign_bit == 1 {
        lemma_mod_add_multiples_vanish(bytes32_to_nat(s_before) as int, pow2(255) as int);
    }
};
```

## Common Lemma Reference

### Byte-to-Nat Lemmas (to_nat_lemmas.rs)
- `lemma_bytes32_to_nat_lower_bound(bytes, index)` - Get lower bound from specific byte
- `lemma_bytes32_to_nat_mod_truncates(bytes, n)` - Modulo truncates to first n bytes
- `lemma_bytes32_to_nat_equals_rec(bytes)` - Connect to recursive definition
- `lemma_decomposition_prefix_rec(bytes, n)` - Split into prefix + suffix
- `lemma_prefix_equal_when_bytes_match` - Equal prefixes from equal bytes

### Power-of-2 Lemmas (pow_lemmas.rs)
- `lemma_pow2_adds(a, b)` - pow2(a) * pow2(b) == pow2(a+b)
- `lemma_pow2_even(n)` - pow2(n) is even for n >= 1
- `lemma_pow2_pos(n)` - pow2(n) > 0
- `lemma2_to64()` - Establishes small powers (2^0 through 2^64)

### Modular Arithmetic Lemmas (div_mod_lemmas.rs)
- `lemma_mod_mod(x, a, b)` - (x % a) % b relates to x % b
- `lemma_mod_add_multiples_vanish(a, m)` - (a + m) % m == a % m
- `lemma_small_mod(x, m)` - If x < m, then x % m == x
- `lemma_mod_bound(x, m)` - x % m < m

### Field-Specific Lemmas (field_specs_u64.rs)
- `pow255_gt_19()` - Proves pow2(255) > 19, thus p() < pow2(255)
- `p_gt_2()` - Proves p() > 2

## Tips

1. **Start simple:** Prove the easiest lemma first to build momentum
2. **Verify often:** Run verification after each small change
3. **Trust existing lemmas:** If a lemma exists, use it - don't reprove
4. **Use reveals sparingly:** Only reveal definitions when necessary
5. **Follow codebase style:** Match existing proof patterns and comments
6. **Ask for help:** Use `by (compute)` for concrete arithmetic, `by (bit_vector)` for bit ops
7. **Document assumptions:** Explain why preconditions are needed
8. **Test with concrete values:** Use specific numbers to validate reasoning
9. **Prefer by-value lemma parameters:** Use `lemma(x: T)` instead of `lemma(x: &T)` for proof lemmas - cleaner ergonomics in proof contexts without borrowing concerns
10. **Remove trivial wrapper specs:** If a spec is just `wrapper(x) = underlying(x, constant)`, remove the wrapper and use the underlying function directly with renamed lemmas
11. **Extract common loop proof logic:** When two loops have similar proof structure, create a helper lemma to reduce duplication
12. **Avoid SMT blowups (`rlimit`):** Keep loop invariants small; avoid unfolding big recursive/`&&&`-heavy specs inside invariants.
13. **Use `#[verifier::opaque]` + targeted `reveal`:**
    - Mark expensive `spec fn` predicates as `#[verifier::opaque]` so Verus doesn't inline them everywhere.
    - Only unfold locally where needed via `reveal(TypeOrModule::spec_fn_name);` inside a helper lemma/proof block.
    - Pattern used in `mul_bits_be`: keep `MontgomeryPoint::ladder_invariant(...)` opaque in the loop invariant, and `reveal(MontgomeryPoint::ladder_invariant);` only inside a small helper lemma (e.g., `lemma_ladder_invariant_swap`) to extract conjuncts.
    - **When to use opaque:** Recursive specs, specs with many `&&&` conjuncts, specs with quantifiers, or any spec causing rlimit timeouts.
    - **When NOT to use opaque:** Simple predicates (e.g., `x < bound`, single field access, trivial arithmetic) where Z3 benefits from seeing the definition inline. Adding opaque to simple specs just creates unnecessary reveal boilerplate.
14. **When quantifiers don't instantiate:** If a callee ensures `forall|k| ...`, add small, explicit `assert(...)` facts (often with the right trigger shape) right before the call to help Verus/Z3 pick the intended instantiation.

## Example Invocation

When you encounter a proof with `admit()` or `assume(...)`:

1. **Understand:** What property needs to be proven?
2. **Search:** Are there existing lemmas that help?
3. **Structure:** Add `assume(false)` at key steps
4. **Prove:** Replace assumes incrementally using patterns above
5. **Verify:** Test each step and the full integration
6. **Clean:** Remove redundant assertions, add comments

## Success Criteria

- All `admit()` and `assume(...)` replaced with actual proofs
- Verification passes: `cargo verus verify`
- Proofs follow codebase style (comments, structure)
- Existing lemmas reused wherever possible
- No exec/ghost mode errors
- Minimal, clean assertions (tested by removal)

## Final Summary Requirements

At the end of a proof session, provide a summary that includes:

1. **Functions proven:** List each function and its status (fully proven, partially proven with remaining assumes)
2. **Lemmas added:** List new lemmas created and their purpose
3. **Specification changes:** Report any preconditions or postconditions that were strengthened, including:
   - Which function's spec was changed
   - What the old spec was (briefly)
   - What the new spec is
   - Why the change was necessary
4. **Remaining work:** If assumes remain, explain what would be needed to complete the proofs
