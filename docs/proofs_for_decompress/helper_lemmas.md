# Helper Lemmas (Undocumented in Main Proofs)

These 18 lemmas are used internally by the main decompress proof chain but are not documented in `decompress_proof.md` or `step1_math_to_verus_mapping.md` because they are implementation details rather than key proof steps.

---

## Field Algebra Helpers (`field_algebra_lemmas.rs`)

| Lemma | Statement | Used By |
|-------|-----------|---------|
| `lemma_a_times_inv_ab_is_inv_b` | a · inv(a·b) = inv(b) | `sqrt_ratio_lemmas.rs` |
| `lemma_double_negation` | -(-x) = x in F_p | `sqrt_ratio_lemmas.rs` |
| `lemma_field_mul_assoc` | (a·b)·c = a·(b·c) | internal |
| `lemma_field_mul_comm` | a·b = b·a | `sqrt_ratio_lemmas.rs` |
| `lemma_inv_of_inv` | inv(inv(x)) = x | `sqrt_ratio_lemmas.rs` |
| `lemma_neg_a_times_inv_ab` | (-a)·inv(a·b) = -inv(b) | `sqrt_ratio_lemmas.rs` |
| `lemma_neg_one_times_is_neg` | (-1)·x = -x | internal |
| `lemma_product_of_squares_eq_square_of_product` | a²·b² = (a·b)² | internal |
| `lemma_solve_for_left_factor` | a·b = c ⟹ a = c·inv(b) | `sqrt_ratio_lemmas.rs` |

---

## Modular Arithmetic Helpers (`div_mod_lemmas.rs`)

| Lemma | Statement | Used By |
|-------|-----------|---------|
| `lemma_double_neg_mod` | (p - (p - x)) % p = x % p | `sqrt_ratio_lemmas.rs` |
| `lemma_mul_by_minus_one_is_negation` | (p-1)·x % p = (p - x%p) % p | `sqrt_ratio_lemmas.rs` |
| `lemma_mul_distributes_over_neg_mod` | a·(p-b) % p = (p - a·b%p) % p | `sqrt_ratio_lemmas.rs` |

---

## Number Theory Helpers (`number_theory_lemmas.rs`)

| Lemma | Statement | Used By |
|-------|-----------|---------|
| `lemma_p_mod_8_eq_5` | p ≡ 5 (mod 8) | `field.rs` (sqrt_ratio_i) |
| `lemma_square_of_complement` | (p-x)² % p = x² % p | `field_algebra_lemmas.rs` |

---

## Constants/Limb Bounds Helpers

| Lemma | Location | Statement | Used By |
|-------|----------|-----------|---------|
| `lemma_edwards_d_limbs_bounded_54` | `edwards_lemmas/constants_lemmas.rs` | EDWARDS_D limbs < 2^54 | `decompress_lemmas.rs` |
| `lemma_one_limbs_bounded_54` | `field_lemmas/constants_lemmas.rs` | ONE limbs < 2^54 | `decompress_lemmas.rs` |

These are 54-bit variants needed for `sqrt_ratio_i` preconditions. The 51-bit versions are documented in the main proofs.

---

## Step1 Internal Helpers

| Lemma | Location | Statement | Used By |
|-------|----------|-----------|---------|
| `lemma_step1_curve_semantics` | `step1_lemmas.rs` | Connects sqrt_ratio_i result to curve membership | `lemma_step1_case_analysis` |
| `lemma_step1_limb_bounds_established` | `decompress_lemmas.rs` | Establishes limb bounds for field ops | `edwards.rs` (step_1) |

---

## Statistics

| Category | Documented | Undocumented | Total |
|----------|------------|--------------|-------|
| Decompress proof chain | 36 | 0 | 36 |
| Helper/utility lemmas | 0 | 18 | 18 |
| **Total new proof fns** | **36** | **18** | **54** |

Coverage: 67% of new lemmas are in the main documentation (the proof chain), 33% are helpers.
