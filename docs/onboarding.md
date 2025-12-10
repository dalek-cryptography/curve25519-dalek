# Verus and Dalek-Lite onboarding guide

This document aims to provide new (prospective) contributors with some recommended first steps, when starting out with this repository. Following these steps should equip you with the basic knowledge and resources needed to start working independently.

## (Optional) Familiarize yourself with Rust
Dalek-Lite is a fork of [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek), and as such, is written in Rust. For the purposes on writing proofs, one does not need a deep understanding of all of Rust's nuances, but contributors with no prior Rust experience should read the [Rust handbook](https://doc.rust-lang.org/book/title-page.html) and make sure they're familiar with at least the following concepts:
  - Bounded integer arithmetic and overflow handling
  - Arrays
  - References
  - Traits

We recommend reading at least chapters 1-4, 7, and 10.

## Familiarize yourself with Verus
Similar to knowing Rust to understand the code, to write proofs _about_ Rust, you have to know Verus. The [Verus guide](https://verus-lang.github.io/verus/guide/) is a critical resource, and we strongly recommend reading at least the first 13 chapters, as well as chapters 30 and 31 (in the Reference section).

Verus also provides a standard library of lemmas, `vstd`, which covers most basic arithmetic rules (e.g. distributivity of multiplication) available [here](https://verus-lang.github.io/verus/verusdoc/vstd/index.html). The `vstd` documentation allows one to look up lemmas by name, but we also recommend cloning the [Verus repository](https://github.com/verus-lang/verus/tree/main) and using your IDE to browse `vstd` locally, since you can use e.g. regex search to find lemmas by "shape" within the `vstd` files.

## Set up Verus tooling
Follow the Verus [installation instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md), but instead of "latest" use the version of Verus currently [used by our CI](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/.github/workflows/ci.yml) (Search for "Install Verus").
If you've set everything up correctly, you should be able to run `cargo-verus verify` in the `curve25519-dalek` directory without errors.

Verus has two "calling modes", `verus <file>.rs` and `cargo-verus verify`. The former only works on single files without dependencies, so it is of limited use beyond training examples, we primarily use the latter.
We recommend using `cargo-verus verify -- --verify-only-module <...>` or `--verify-function` to narrow verification while you're testing a new proof.

## Solve some introductory problems
To start, we have curated a few short, but nontrivial, proof exercises. Your goal is to fill in the `...` sections, such that `cargo-verus verify` (resp. `verus`) succeeds.
All of these lemmas are already proven and require only `vstd` lemmas. The solutions are part of this repository's `common_lemmas`, so after finishing this section, you can compare. 

1. Right-shift decomposition
```rust
// v >> (a + b) == (v >> a) >> b
pub proof fn lemma_shr_by_sum(v: u64, a: nat, b: nat)
    requires
        (a + b) < 64,
    ensures
        (v >> (a + b)) == ((v >> a) >> b)
{
    ...
}
```
2. `pow2` multiplication bound
```rust
pub proof fn lemma_pow2_mul_bound_general(a: nat, s: nat, k: nat)
    requires
        a < pow2(s),
    ensures
        pow2(k) * a <= pow2(k + s) - pow2(k),
        a * pow2(k) <= pow2(k + s) - pow2(k),
        pow2(k + s) - pow2(k) < pow2(k + s),
{
    ...
}
```
3. Bit masking bound
```rust
pub proof fn lemma_u64_masked_lt(v: u64, k: nat)
    requires
        0 <= k < 64,
    ensures
        v & (low_bits_mask(k) as u64) < (1u64 << k),
{
    ...
}
```

## Familiarize yourself with our `common_lemmas`
In addition to `vstd`, we curate a collection of general math lemmas, which you may find useful when writing proofs. They are found in [`common_lemmas`][common], and act as an extension of `vstd`. Spend some time reading these lemmas, to get a general feeling for the properties that have already been proven, so you can avoid reproving them yourself later.

## Read our Style Guide
The style guide outlines basic guidelines to help keep our codebase, especially proofs, readable and maintainable, and can be found [here][style].

## Contribute
There's plenty of resources online teaching git and good git hygiene, so spend some time familiarizing yourself with the additional overhead of PR-driven teamwork. Below, we briefly summarize what we consider a clean contribution loop.
When preparing a new contribution, do the following:

1. Find (or create) an [issue](https://github.com/Beneficial-AI-Foundation/dalek-lite/issues) you plan to work on. **❗If creating a new issue, make sure it's on `dalek-lite`, and _not_ the parent repo curve25519 that is being forked.❗**
Check that you're assigned to it, and that the issue is allocated to the correct project. Change its status to "In Progress"
1. Make sure your `main` branch is up-to-date (`git fetch/pull`)
1. Create a new local branch from the latest `main` with a sensible name (`git checkout -b <...>`). Some of us use the convention `xy/name`, where `xy` are the author initials.
1. Add your code changes, split into commits as necessary. Changes should follow our [style guide][style].
1. Check if `main` has been updated while you were adding code changes (`git fetch`). If yes, `git rebase origin/main` to make sure you're caught up with the latest changes on your new branch too. You might need to resolve conflicts at this point, if any.
1. Fix formatting (`find . -name "*.rs" -type f | xargs verusfmt`) and commit the `verusfmt` changes, if any.
1. Ensure `cargo-verus verify` succeeds locally.
1. Push your local branch to remote (`git push`). There's a local git setting to always push `abc` to `origin/abc` you might want enabled.
1. Open a PR and request a review from `curve-dalek-team`. **❗Make sure it's against `dalek-lite`, and _not_ the parent repo curve25519 that is being forked.❗** Add `closes #XYZ` to the PR body, referencing the issue that is being addressed by this PR. Write a meaningful summary of the changes, especially highlighting any changes to existing code (e.g. "added xyz to the `ensures` clause of `lemma_foo`", "moved `lemma_bar` to abc", "renamed `lemma_baz` to `lemma_baz_aux`", etc.)
1. After receiving feedback, address any comments, and mark them as resolved when appropriate. 
1. Merge after all critical comments have been addressed and all required checks pass

[style]: ./style_guide.md
[common]: https://github.com/Beneficial-AI-Foundation/dalek-lite/tree/main/curve25519-dalek/src/lemmas/common_lemmas