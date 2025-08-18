# Development Notes

## Fiat Backend Testing

To test compilation with the fiat backend:
```bash
RUSTFLAGS='--cfg curve25519_dalek_backend="fiat"' cargo check
```

## Verus docs
See https://verus-lang.github.io/verus/guide/ for tutorial

See https://verus-lang.github.io/verus/verusdoc/vstd for vstd lemmas, 
especially https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/index.html 
for mul and div_mod lemmas. 
You may need to click on the specific lemma link to see the statement of the lemma. 
Feel free to click on many links to look for the best lemma.

## Verus Verification

Run Verus verification from the `curve25519-dalek` directory:
```bash
cd curve25519-dalek && cargo verus verify -- --multiple-errors 20
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

### 12. Using the Verus Cleaner Script

The `verus_cleaner.py` script automates the process of testing whether proof statements are necessary or redundant. It systematically removes each matching statement, runs verification, and reports which ones can be safely removed.

It must be run from the root `curve25519-dalek`, not from `curve25519-dalek/curve25519-dalek`.

#### Basic Usage

```bash
scripts/verus_cleaner.py <file_path> <start_line> <end_line> '<pattern>'
```

- `end_line` is inclusive
- `pattern`: Regex pattern to match statements to test

**Important**: Due to shell interpretation issues, pipe characters (`|`) in regex patterns don't work properly. Use separate commands instead:

#### Examples

**Clean broadcasts and lemmas (run separately):**
```bash
scripts/verus_cleaner.py src/backend/serial/u64/scalar_verus.rs 200 210 'broadcast'
scripts/verus_cleaner.py src/backend/serial/u64/scalar_verus.rs 200 210 'lemma'
```

**Clean assert statements:**
```bash
scripts/verus_cleaner.py src/backend/serial/u64/field_verus.rs 150 200 'assert'
```

### 13. Moving Proof Blocks to Lemmas

Executable code is easier to read if multiline proof blocks are replaced by lemmas:
1. Replace the proof block with an assume statement that you think will show the same thing.
2. Replace that with a lemma that shows the same thing. You can assume false for the lemma. 
3. Put the contents of the proof block into the lemma to actually prove it. 

Verify at each step

### 14. Replacing broadcasts

For certain lemmas, `broadcast use <lemma>` is a convenient way 
to apply the lemma one or more times without specifying the arguments.
But it can cause the proof to time out because the SMT solver has to do more work. 

When asked to replace a broadcast, find the exact statement of the lemma
(this typically means you should look in the vstd docs), and then think
about what call (or calls) to the lemma the broadcast is implicitly doing.
