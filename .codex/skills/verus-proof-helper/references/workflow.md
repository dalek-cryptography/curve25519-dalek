# Workflow

## Phase 1: Understand the proof goal

1. Read the function signature and `ensures`/`requires` to identify the *exact* goal.
2. Locate any `admit()`/`assume(...)`/`assume(false)` placeholders and list what each one stands in for.
3. Check nearby comments and helper lemmas in the same module.

## Phase 2: Reuse existing lemmas first

Do not reinvent lemmas. Start with `references/lemma-reference.md` and search in this order:

1. Same file / same module
2. Common lemmas (byte/nat, pow2, div/mod, bit lemmas)
3. Domain folders (field/edwards/montgomery/etc.)

If you *must* add a new lemma, prefer the smallest specialized lemma that unblocks the proof, and only generalize later.

## Phase 3: Develop incrementally (moving `assume(false)`)

Use the “moving `assume(false)`” technique to keep the prover focused and the diff reviewable:

```rust
proof fn my_lemma(...) {
    // Step 1: establish context / unfold the right defs
    lemma_setup(...);
    assume(false);

    // Step 2: prove a key intermediate claim
    assert(intermediate_fact);
    assume(false);

    // Step 3: conclude
    assert(final_result);
}
```

Rules of thumb:

- Replace one `assume(false)` at a time and re-verify.
- Keep intermediate `assert`s that help the SMT solver.
- Prefer short helper lemmas over huge proof blocks.

## Phase 4: Apply techniques

Use `references/techniques.md` for a menu of tactics (`bit_vector`, `nonlinear_arith`, decomposition, `calc!`, induction, loop invariants, opaque+`reveal`, etc.).

## Phase 5: Handle common issues

If you hit errors like mode mismatches, array interpretation problems, quantifiers not instantiating, or `rlimit`, use `references/common-issues.md`.

## Phase 6: Verify and clean up

Verify incrementally:

```bash
cargo verus verify -- --verify-only-module module_name --verify-function function_name
```

Verify integration:

```bash
cargo verus verify -- --verify-module module_name
```

Format (when the repo uses `verusfmt`):

```bash
verusfmt path/to/changed1.rs path/to/changed2.rs
```

Then re-run `cargo verus verify ...` to ensure formatting didn’t perturb proof blocks.

Cleanup checklist:

- Remove redundant assertions (delete one at a time; re-verify).
- Prefer `assert(...)` over `assert(...) by { ... }` when the `by` block has no real lemma calls.
- Move lemma calls into the `assert .. by { ... }` block they justify (one lemma per assertion when possible).
- Keep comments concise and explain *why*, not *what*.
- Remove unused general lemmas after a specialized lemma fully replaces them (search usages before deleting).
