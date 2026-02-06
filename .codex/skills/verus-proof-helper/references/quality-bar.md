# Quality bar

## Example invocation checklist

When you encounter a proof with `admit()` or `assume(...)`:

1. Understand: what property needs to be proven?
2. Search: what existing lemmas apply?
3. Structure: add `assume(false)` at key steps.
4. Prove: replace `assume(false)` one at a time using targeted tactics.
5. Verify: verify each step, then verify the module/integration.
6. Clean: remove redundant asserts, keep comments concise.

## Success criteria

- All `admit()` and `assume(...)` replaced with actual proofs (or explicitly listed as remaining work).
- Verification passes (e.g., `cargo verus verify`).
- Proofs follow codebase style (structure, comments, placement of lemma calls).
- Existing lemmas are reused wherever possible.
- No exec/ghost mode errors.
- Assertions are minimal and intentional (confirmed by removal testing).

## End-of-session summary requirements

Provide a brief summary that includes:

1. Functions proven: each function and its status (fully proven / partially proven with remaining assumes).
2. Lemmas added: each new lemma and why it exists.
3. Spec changes: any strengthened preconditions/postconditions (what changed and why).
4. Remaining work: what would be needed to finish if anything remains.
