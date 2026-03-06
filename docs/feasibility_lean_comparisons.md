# Verus Axioms vs. Lean 4 / Mathlib: Side-by-Side Definitions

Companion to [feasibility_lean.md](feasibility_lean.md). For each axiom, the Verus
definition is shown alongside the closest existing Lean 4 / Mathlib theorem or
definition.

---

## 1. Primality

### axiom_p_is_prime

**Verus:**
```rust
pub proof fn axiom_p_is_prime()
    ensures is_prime(p()),   // p() = 2^255 - 19
{ admit(); }
```

**Lean 4 (Mathlib):** `lucas_primality` — the Lucas test for primes
```lean
theorem lucas_primality (p : ℕ) (a : ZMod p)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ (q : ℕ), Nat.Prime q → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) :
    Nat.Prime p
```
Source: [`Mathlib.NumberTheory.LucasPrimality`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LucasPrimality.html)

**Gap:** Need to supply a witness `a` and the full factorisation of `p - 1`, then verify the modular exponentiations via `native_decide`.

---

### axiom_group_order_is_prime

**Verus:**
```rust
pub proof fn axiom_group_order_is_prime()
    ensures is_prime(group_order()),   // L = 2^252 + 277423...
{ admit(); }
```

**Lean 4:** Same `lucas_primality` applied to `L`.

---

## 2. Quadratic Residuosity

### axiom_486660_not_quadratic_residue

**Verus:**
```rust
pub proof fn axiom_486660_not_quadratic_residue()
    ensures !is_square(486660nat),
{ admit(); }
```

**Lean 4 (Mathlib):** `quadraticChar_neg_one_iff_not_isSquare`
```lean
theorem quadraticChar_neg_one_iff_not_isSquare {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {a : F} :
    (quadraticChar F) a = -1 ↔ ¬ IsSquare a
```
Source: [`Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.html)

Combined with Euler's criterion:
```lean
theorem quadraticCharFun_eq_pow_of_char_ne_two {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1
```

**Gap:** Instantiate `F = ZMod p`, compute `(486660 : ZMod p) ^ ((p-1)/2)` via `native_decide`.

---

### axiom_sqrt_m1_not_square / axiom_neg_sqrt_m1_not_square

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_not_square()
    ensures !is_square(sqrt_m1()),
{ admit(); }

pub proof fn axiom_neg_sqrt_m1_not_square()
    ensures !is_square((p() - sqrt_m1()) as nat),
{ admit(); }
```

**Lean 4:** Same `quadraticChar_neg_one_iff_not_isSquare`. For the general theory that square roots of −1 are non-squares when p ≡ 5 (mod 8):
```lean
theorem ZMod.exists_sq_eq_neg_one_iff {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    (∃ y : ZMod p, y ^ 2 = -1) ↔ p % 4 ≠ 3
```
Source: [`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html)

---

### axiom_sqrt_m1_squared

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_squared()
    ensures (sqrt_m1() * sqrt_m1()) % p() == (p() - 1),
{ admit(); }
```

**Lean 4:** No direct theorem for a specific constant. Use `ZMod p` arithmetic:
```lean
-- Verify by computation over ZMod p
example : ((SQRT_M1 : ZMod p) ^ 2 = -1) := by native_decide
```

Where `ZMod` is from [`Mathlib.Data.ZMod.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html) and provides a `Field` instance when `p` is prime.

---

## 3. Edwards Curve Group Law

### axiom_edwards_add_associative

**Verus:**
```rust
pub proof fn axiom_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
    ensures
        edwards_add(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1, x3, y3)
        == edwards_add(x1, y1, edwards_add(x2, y2, x3, y3).0, edwards_add(x2, y2, x3, y3).1),
{ admit(); }
```

**Lean 4 (Mathlib):** Weierstrass curve abelian group (nearest analogue):
```lean
instance WeierstrassCurve.Jacobian.Point.instAddCommGroup :
    AddCommGroup (WeierstrassCurve.Jacobian.Point W) := ...
-- This gives: ∀ a b c, (a + b) + c = a + (b + c)   [via add_assoc]
```
Source: [`Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.html)

**Gap:** This is for Weierstrass curves. No Edwards curve definition exists in Mathlib. Would need to either define twisted Edwards curves directly (following Hales & Raya's polynomial identity approach) or establish a birational equivalence to Weierstrass.

---

### axiom_edwards_add_complete

**Verus:**
```rust
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires is_on_edwards_curve(x1, y1), is_on_edwards_curve(x2, y2),
    ensures
        field_add(1, t) != 0 && field_sub(1, t) != 0,   // denominators nonzero
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{ admit(); }
```

**Lean 4 (Mathlib):** Nearest for Weierstrass:
```lean
theorem WeierstrassCurve.Jacobian.nonsingular_add {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular (W.add P Q)
```

**Gap:** Edwards completeness (denominators nonzero when d is non-square) is a fundamentally different statement. Not in Mathlib.

---

### axiom_edwards_scalar_mul_signed_additive

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures
        edwards_add(edwards_scalar_mul_signed(P, a), edwards_scalar_mul_signed(P, b))
        == edwards_scalar_mul_signed(P, a + b),
{ admit(); }
```

**Lean 4 (Mathlib):** Once a group is defined, this is a basic property:
```lean
theorem add_zsmul {G : Type} [AddCommGroup G] (a b : ℤ) (g : G) :
    (a + b) • g = a • g + b • g
```
Source: [`Mathlib.Algebra.Group.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html) (via `SubNegMonoid`)

---

### axiom_edwards_scalar_mul_distributive

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_distributive(a: (nat, nat), b: (nat, nat), n: nat)
    ensures
        edwards_scalar_mul(edwards_add(a.0, a.1, b.0, b.1), n)
        == edwards_add(edwards_scalar_mul(a, n), edwards_scalar_mul(b, n)),
{ admit(); }
```

**Lean 4 (Mathlib):** Once a group is defined:
```lean
-- The "multiply by n" map is an AddMonoidHom
theorem AddMonoidHom.map_add {G H : Type} [AddCommMonoid G] [AddCommMonoid H]
    (f : G →+ H) (a b : G) : f (a + b) = f a + f b
```
Source: [`Mathlib.Algebra.Group.Hom.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html)

---

## 4. Montgomery Curve

### axiom_montgomery_add_associative

**Verus:**
```rust
pub proof fn axiom_montgomery_add_associative(P: MontgomeryAffine, Q: MontgomeryAffine, R: MontgomeryAffine)
    ensures montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{ admit(); }
```

**Lean 4:** No Montgomery curve in Mathlib. Nearest: same `instAddCommGroup` for Weierstrass.

---

### axiom_xdbl_projective_correct / axiom_xadd_projective_correct

**Verus (xDBL):**
```rust
pub proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires projective_represents_montgomery_or_infinity_nat(U, W, P),
    ensures projective_represents_montgomery_or_infinity_nat(
        spec_xdbl_projective(U, W).0, spec_xdbl_projective(U, W).1,
        montgomery_add(P, P)),
{ admit(); }
```

**Lean 4:** No existing theorem. Pattern from Weierstrass:
```lean
-- Doubling formula polynomial for Weierstrass Jacobian
def WeierstrassCurve.Jacobian.dblX (P : Fin 3 → R) : R := ...
def WeierstrassCurve.Jacobian.dblY (P : Fin 3 → R) : R := ...
def WeierstrassCurve.Jacobian.dblZ (P : Fin 3 → R) : R := ...
```
Source: [`Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.html)

---

## 5. Birational Equivalence

### axiom_edwards_to_montgomery_preserves_validity

**Verus:**
```rust
pub proof fn axiom_edwards_to_montgomery_preserves_validity(x: nat, y: nat)
    requires is_on_edwards_curve(x, y),
    ensures is_valid_u_coordinate(montgomery_u_from_edwards_y(y)),
{ admit(); }
```

**Lean 4:** No direct theorem. Nearest framework:
```lean
-- Isomorphism between curves with same j-invariant
def WeierstrassCurve.IsomOfJ ... : VariableChange ...
```
Source: [`Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.html)

The specific Edwards → Montgomery map u = (1+y)/(1−y) would need to be defined and verified with the `ring` tactic.

---

### axiom_edwards_to_montgomery_commutes_with_scalar_mul

**Verus:**
```rust
pub proof fn axiom_edwards_to_montgomery_commutes_with_scalar_mul(x: nat, y: nat, n: nat)
    requires is_on_edwards_curve(x, y),
    ensures
        montgomery_u_from_edwards_y(edwards_scalar_mul((x, y), n).1)
        == montgomery_scalar_mul_u(montgomery_u_from_edwards_y(y), n),
{ admit(); }
```

**Lean 4:** Once the map is an `AddMonoidHom`:
```lean
theorem AddMonoidHom.map_nsmul {M N : Type} [AddMonoid M] [AddMonoid N]
    (f : M →+ N) (n : ℕ) (a : M) : f (n • a) = n • f a
```

---

## 6. Subgroup Closure

### axiom_even_subgroup_closed_under_add

**Verus:**
```rust
pub proof fn axiom_even_subgroup_closed_under_add(p1: EdwardsPoint, p2: EdwardsPoint)
    requires
        is_in_even_subgroup(p1), is_in_even_subgroup(p2),
        is_well_formed_edwards_point(p1), is_well_formed_edwards_point(p2),
    ensures
        forall|result: EdwardsPoint|
            /* result = p1 + p2 */ ==> is_in_even_subgroup(result),
{ admit(); }
```

**Lean 4 (Mathlib):**
```lean
theorem AddSubgroup.add_mem {G : Type} [AddGroup G] {H : AddSubgroup G}
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a + b ∈ H
```
Source: [`Mathlib.Algebra.Group.Subgroup.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Defs.html)

The image of the "double" endomorphism is automatically a subgroup in Lean once the group is defined.

---

## 7. Inverse Square Root

### axiom_invsqrt_factors_over_square

**Verus:**
```rust
pub proof fn axiom_invsqrt_factors_over_square(a: nat, b: nat)
    requires a % p() != 0, b % p() != 0,
    ensures nat_invsqrt(field_mul(a, field_square(b)))
         == field_abs(field_mul(nat_invsqrt(a), field_inv(b))),
{ admit(); }
```

**Lean 4:** Standard field algebra via:
```lean
theorem mul_inv_cancel₀ {α : Type} [GroupWithZero α] {a : α} (ha : a ≠ 0) :
    a * a⁻¹ = 1

-- IsSquare predicate
def IsSquare {α : Type} [Mul α] (a : α) : Prop := ∃ r, a = r * r
```
Source: [`Mathlib.Algebra.Group.Even`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Even.html)

---

## 8. Hash Properties

### axiom_sha512_output_length

**Verus:**
```rust
pub proof fn axiom_sha512_output_length(input: Seq<u8>)
    ensures spec_sha512(input).len() == 64,
{ admit(); }
```

**Lean 4:** No SHA-512 spec exists. SHA-3 was formalised by Doussot (2024). A minimal spec:
```lean
-- Hypothetical definition
def SHA512 (input : ByteArray) : ByteArray := ...
axiom SHA512_output_length : ∀ input, (SHA512 input).size = 64
```

---

## 9. Probability / Uniformity

### axiom_uniform_point_add

**Verus:**
```rust
pub proof fn axiom_uniform_point_add(p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires
        /* sum = p1 + p2 */,
        is_uniform_ristretto_point(p1), is_uniform_ristretto_point(p2),
        is_independent_uniform_ristretto_points(p1, p2),
    ensures is_uniform_ristretto_point(sum),
{ admit(); }
```

**Lean 4 (Mathlib):** Framework:
```lean
def PMF.uniformOfFintype (α : Type) [Fintype α] [Nonempty α] : PMF α :=
    ofFinset Finset.univ (fun a => (↑(Fintype.card α))⁻¹) ...
```
Source: [`Mathlib.Probability.Distributions.Uniform`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Uniform.html)

The group-theoretic result (uniform + independent → uniform sum) would combine this with `AddMonoidHom` properties. No existing specialised theorem.

---

## 10. Ristretto / Elligator (no existing Lean counterparts)

All Ristretto and Elligator axioms (`axiom_elligator_on_curve`, `axiom_elligator_in_even_subgroup`, `axiom_ristretto_cross_mul_iff_equivalent`, `axiom_ristretto_decode_on_curve`, `axiom_ristretto_decode_in_even_subgroup`, `axiom_elligator_nonzero_intermediates`, `axiom_elligator_encode_outputs_valid_u`) have **no existing counterpart** in Lean / Mathlib. These would all require novel formalisations.

---

## 11. Precomputed Tables (no existing Lean counterparts)

`axiom_ed25519_basepoint_table_valid`, `axiom_affine_odd_multiples_of_basepoint_valid`, `axiom_ristretto_basepoint_table_valid` — all computational verification; no existing theorems.
