---
name: verus-proof-helper
description: Help complete and debug Verus proofs in verified-cryptography Rust codebases (e.g., curve25519-dalek). Use when replacing `admit()`/`assume(...)`, proving byte/nat conversions + bounds, bit-vector facts, modular arithmetic, writing loop invariants, strengthening specs, or handling Verus `rlimit`/timeout issues via opaque specs + targeted `reveal`.
---

# Verus Proof Helper

## Quick start

- Identify the exact goal (postcondition/lemma) and list remaining `admit()`/`assume(...)`.
- Search for existing lemmas before writing new ones (`references/lemma-reference.md`).
- Sketch the proof with the “moving `assume(false)`” technique; verify after each replacement (`references/workflow.md`).
- Apply targeted tactics (`bit_vector`, `nonlinear_arith`, `calc!`, induction, decomposition) (`references/techniques.md`).
- If Verus is stuck (`rlimit`, quantifier instantiation, mode errors), apply the fixes in `references/common-issues.md`.
- Finish by simplifying assertions and writing a short wrap-up (`references/quality-bar.md`).

## Crypto codebases: common tips

- Cache exec-only calls (e.g., `invert()`) into locals; don’t call exec fns inside `proof {}` blocks (`references/patterns.md`).
- Preserve executable code as much as possible; when refactoring is needed for verification, keep it targeted and record the original snippet with `/* ORIGINAL CODE: ... */` (or `// ORIGINAL CODE:`) near the change.
- When specs give only “representation-level” facts (e.g., limb equality), explicitly lift them to semantic equality (field value / struct equality) (`references/patterns.md`).
- If direct equality is awkward/unsupported, compare canonical encodings (bytes/limbs) using existing helper APIs and reason about their specs (`references/patterns.md`).
- Don’t duplicate equality work: if `==` is already specified via canonical bytes or `ct_eq`, branch on `==` and then use its `ensures` to bridge to the spec fact you need (`references/patterns.md`, `references/common-issues.md`).
- If you hit rarer tool limitations (e.g., `by (compute)` stability), see `references/common-issues.md`.
- If the repo uses `verusfmt`, run it on touched files before final verification/commit (`references/workflow.md`).

## Reference map

- `references/workflow.md`: step-by-step workflow + verification commands
- `references/lemma-reference.md`: where to look + common lemma names/patterns
- `references/techniques.md`: proof tactics and patterns (including opaque + `reveal`)
- `references/common-issues.md`: common Verus error messages and fixes
- `references/patterns.md`: worked mini-patterns from “compress” proof work
- `references/quality-bar.md`: success criteria and end-of-session summary checklist
