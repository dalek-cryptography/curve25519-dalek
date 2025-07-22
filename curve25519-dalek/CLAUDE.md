# Development Notes

## Verus Verification

Run Verus verification from the `curve25519-dalek` directory:
```bash
cd curve25519-dalek && cargo verus verify -- --multiple-errors 5
```

This ensures proper compilation and avoids dependency issues with other crates in the workspace.

## Strategies for Debugging Verus Proofs

### 1. Replace `assume(false)` with `assert` to Find Issues
When encountering `assume(false)` statements, replace them with `assert` to see what Verus cannot prove. The error messages will point to the specific properties that need verification.

### 2. Analyze Overflow Errors by Removing All Bounds
When facing "possible arithmetic overflow" errors:
- Remove all loop invariants and bounds temporarily
- Run verification to see the raw overflow locations
- This reveals what bounds are actually needed to prevent overflow

### 3. Use Iteration-Dependent Loop Invariants
For loops where values grow over iterations:
- Instead of fixed bounds like `x < 2^54`, use `x < 2^(base + i)`
- This allows values to grow incrementally while maintaining bounds
- Example: `carry < (1u64 << (52 + i as u64))` for a 5-iteration loop

### 4. Test Necessity of Assumptions
When you have multiple `assume` statements:
- Remove them one by one to see which are actually necessary
- This identifies the minimal set of assumptions needed
- Helps focus proof efforts on the essential constraints

### 5. Break Down Complex Assertions
When a complex assertion fails:
- Add separate `assume` statements for each component
- Then try to `assert` the combination
- This isolates whether the issue is individual bounds or their combination
- Example: If `assert(a + b + c < bound)` fails, try assuming bounds on `a`, `b`, `c` separately

### 6. Study Working Examples for Patterns
Look at similar verified code (like `field_verus.rs`) to understand:
- Common proof patterns and lemma usage
- How bounds are established and maintained
- Typical `proof { ... }` block structures
- Use of vstd lemmas like `lemma_pow2_pos`, `lemma_mul_strict_inequality`

### 7. Mathematical Reasoning vs Formal Proof
Remember that:
- Sound mathematical reasoning in comments doesn't automatically translate to Verus proofs
- Even obvious mathematical facts need explicit proof steps using vstd lemmas
- `assume` statements verify mathematical structure but don't constitute formal proofs
- Convert assumes to proper proofs incrementally using appropriate lemmas

### 8. Be Careful with Bit Shifting
When working with bit shifts in Verus proofs:
- **Important**: `1u128 << 128` evaluates to 0, not 2^128!
  - u128 only has 128 bits, so shifting by 128 positions shifts all bits out
  - The maximum meaningful shift for u128 is 127 bits
  - For pow2(128), use vstd's `pow2` function instead of bit shifting
- Use vstd's `pow2` and related lemmas for large power-of-2 values

### 9. Incremental Proof Strategy: Moving assume(false)
A powerful technique for gradually proving complex functions:
- Start with `assume(false)` at the beginning of the function body
- Move it down one line at a time, proving each line as you go
- When Verus reports an error, add the necessary proof block before that line
- This approach lets you:
  - Focus on one verification challenge at a time
  - Build confidence incrementally as each line passes verification
  - Identify the exact point where overflow or other issues occur
- Example: In `square_internal`, moved `assume(false)` from after `z[0]` to after `z[1]`, requiring a proof that `m(...) * 2` doesn't overflow
- Continue until `assume(false)` reaches the end of the function
