# Development Notes

## Verus Verification

Run Verus verification from the `curve25519-dalek` directory:
```bash
cd curve25519-dalek && cargo verus verify -- --multiple-errors 20
```

This ensures proper compilation and avoids dependency issues with other crates in the workspace.

## Proving Polynomial Arithmetic in Verus

### When proving polynomial multiplication/squaring postconditions

**Situation**: You have a function that computes polynomial operations (like squaring) and need to prove the result equals a mathematical expression.

**Try this approach**:

1. **Expand both sides explicitly** - Create intermediate variables that show the polynomial structure:
   ```rust
   let a0 = a.limbs[0] as nat;
   let a1 = a.limbs[1] as nat;
   // ... etc
   
   let left_side = (z[0] as nat) + (z[1] as nat) * pow2(52) + ...;
   let right_side = polynomial * polynomial;
   ```

2. **Create an intermediate representation** - Show what the computation *should* produce:
   ```rust
   let left_side_expanded = (a0 * a0) + 
                           (2 * a0 * a1) * pow2(52) + 
                           (2 * a0 * a2 + a1 * a1) * pow2(104) + ...;
   ```

3. **Break the proof into two parts**:
   - Prove `left_side_expanded == right_side` (mathematical equivalence)
   - Prove `left_side == left_side_expanded` (implementation correctness)

### When connecting exec-mode computations to spec-mode assertions

**Situation**: You have functions like `m(x,y)` that compute values in exec mode, but need to prove properties about them in spec/proof mode.

**What works**:
- Simple cases like `z[0] = m(a,a)` proving `(z[0] as nat) == a * a` often work automatically
- Verus understands the postcondition `m(x,y) == x * y` for the direct multiplication

**What doesn't work automatically**:
- Complex expressions like `z[1] = m(a,b) * 2` proving `(z[1] as nat) == 2 * a * b`
- Sums of products like `z[2] = m(a,c) * 2 + m(b,b)`
- Verus struggles to connect the exec-mode arithmetic with spec-mode nat arithmetic

### When using nonlinear arithmetic solvers

**Situation**: Default Verus/Z3 can't prove nonlinear arithmetic properties.

**Try nonlinear_arith**:
```rust
assert(property) by(nonlinear_arith)
    requires
        // Add explicit bounds
        a < bound,
        b < bound,
        // Add definitions
        polynomial == a + b * pow2(52),
        // Add relationships
        result == polynomial * polynomial
{
    // Body can provide hints
}
```

**Important**: 
- `nonlinear_arith` needs explicit context in the requires clause
- Bounds on variables are often necessary
- Complex polynomial expansions may still not be provable

**Note**: `integer_ring` is not available as an assert-by prover in current Verus.

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
- Continue until `assume(false)` reaches the end of the function, then remove it
- **Important**: Commit after every successful step to preserve progress and create a clear history

### 10. Version Control Best Practices
For Verus proof development:
- **Commit frequently**: After every successful verification step or meaningful progress
- **Commit early**: Even partial proofs with `assume` statements are valuable progress
- **Clear commit messages**: Describe what was proven and any key insights
- **Preserve working states**: Don't lose progress by making multiple changes without committing
- Use the incremental approach: prove one thing, commit, prove the next thing, commit

### 11. Cleaning Up Redundant Assertions for PR
After proving functions completely, clean up redundant assertions before submitting PRs:

**Process**: For each `assert` statement in your proven functions:
1. Remove the assert statement
2. Run verus as described above.
3. If verification still passes: keep it removed (was redundant)
4. If verification fails: put the assert back (was necessary)
5. Move to the next assert

**IMPORTANT**: When asked to test assertion removal:
- **Test every single assert individually** - do not skip steps or batch similar-looking assertions
- **Be thorough even if it takes many cargo verify runs** - this is exactly the kind of careful, systematic work that LLMs excel at
- **Complete ALL tests when asked** - do not stop halfway through even if patterns become clear
- **Document what you tested and what you didn't** - be explicit about your methodology  
- LLMs can handle repetitive verification tasks that would be tedious for humans
- Taking shortcuts undermines the value of systematic verification
- When asked to test "all" assertions, continue until every single one has been individually tested
 
#### Patterns that are often redundant
- Individual bounds like `assert(m_term1 < (1u128 << 104))` where `m_term1 = m(...)` and the `m()` function postcondition already guarantees the bound
- Intermediate steps in multi-step calculations where only the final result matters
- Duplicate calculations that Verus can derive automatically
