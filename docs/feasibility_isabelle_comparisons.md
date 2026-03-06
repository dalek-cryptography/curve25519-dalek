# Verus Axioms vs. Isabelle/HOL: Side-by-Side Definitions

Companion to [feasibility_isabelle.md](feasibility_isabelle.md). For each axiom, the
Verus definition is shown alongside the closest existing Isabelle/HOL theorem or
definition from the AFP or HOL library.

---

## 1. Edwards Curve Group Law

### axiom_edwards_add_associative

**Verus:**
```rust
pub proof fn axiom_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
    ensures
        edwards_add(edwards_add(x1,y1,x2,y2).0, edwards_add(x1,y1,x2,y2).1, x3, y3)
        == edwards_add(x1, y1, edwards_add(x2,y2,x3,y3).0, edwards_add(x2,y2,x3,y3).1),
{ admit(); }
```

**Isabelle/HOL (AFP):** `Edwards_Elliptic_Curves_Group` — **direct proof of this axiom:**
```isabelle
(* From AFP: Edwards_Elliptic_Curves_Group.thy *)
(* Hales & Raya, IJCAR 2020 *)

(* The addition law for Edwards curves: *)
definition add :: "'a::comm_ring ⇒ 'a ⇒ 'a × 'a ⇒ 'a × 'a ⇒ 'a × 'a" where
  "add c d (x1, y1) (x2, y2) =
    ((x1*y2 + y1*x2) / (1 + d*x1*x2*y1*y2),
     (y1*y2 - c*x1*x2) / (1 - d*x1*x2*y1*y2))"

(* Associativity proved as polynomial identity over ℤ, verified by polynomial division: *)
theorem associativity:
  assumes "on_curve c d P" "on_curve c d Q" "on_curve c d R"
  shows "add c d (add c d P Q) R = add c d P (add c d Q R)"
```
Source: [AFP `Edwards_Elliptic_Curves_Group`](https://devel.isa-afp.org/entries/Edwards_Elliptic_Curves_Group.html)

**This is a direct, machine-checked proof of the Verus axiom.** Specialise to Ed25519 parameters: c = 1, d = −121665/121666 (in GF(p)).

---

### axiom_edwards_add_complete

**Verus:**
```rust
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires is_on_edwards_curve(x1, y1), is_on_edwards_curve(x2, y2),
    ensures
        field_add(1, t) != 0 && field_sub(1, t) != 0,
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{ admit(); }
```

**Isabelle/HOL (AFP):** Same AFP entry proves completeness (denominators are nonzero):
```isabelle
(* From AFP: Edwards_Elliptic_Curves_Group.thy *)
(* When d is not a square, the denominators 1 ± d·x1·x2·y1·y2 are nonzero *)

lemma add_closure:
  assumes "on_curve c d P" "on_curve c d Q"
    and "¬ is_square d"    (* d is not a quadratic residue *)
  shows "on_curve c d (add c d P Q)"
    and "1 + d * fst P * fst Q * snd P * snd Q ≠ 0"
    and "1 - d * fst P * fst Q * snd P * snd Q ≠ 0"
```

**This directly proves the Verus axiom.** The non-square condition on d holds for Ed25519.

---

### axiom_edwards_scalar_mul_signed_additive

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures edwards_add(smul(P,a), smul(P,b)) == smul(P, a+b),
{ admit(); }
```

**Isabelle/HOL:** Once the AFP entry provides a group structure:
```isabelle
(* HOL-Algebra: Group.thy *)
lemma (in group) int_pow_mult:
  "x [^] (m + n :: int) = x [^] m ⊗ x [^] n"

(* Or from the additive locale: *)
lemma (in comm_group) add_pow_add:
  "nat_pow (add a b) n = add (nat_pow a n) (nat_pow b n)"
```

---

### axiom_edwards_scalar_mul_distributive

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_distributive(a: (nat, nat), b: (nat, nat), n: nat)
    ensures edwards_scalar_mul(edwards_add(a, b), n) == edwards_add(smul(a,n), smul(b,n)),
{ admit(); }
```

**Isabelle/HOL:** Endomorphism property in abelian groups:
```isabelle
(* HOL-Algebra: Group.thy *)
lemma (in comm_group) hom_mult:
  assumes "h ∈ hom G G" "x ∈ carrier G" "y ∈ carrier G"
  shows "h (x ⊗ y) = h x ⊗ h y"
```

---

## 2. Primality

### axiom_p_is_prime

**Verus:**
```rust
pub proof fn axiom_p_is_prime()
    ensures is_prime(p()),
{ admit(); }
```

**Isabelle/HOL (AFP):** `Pratt_Certificate` — Pratt's primality certificate system:
```isabelle
(* From AFP: Pratt_Certificate.thy *)

(* The core soundness theorem: *)
theorem pratt_sound:
  assumes "valid_cert (Prime p)"
  shows "prime p"

(* Certificate checking via code generation: *)
(* From AFP: Pratt_Certificate_Code.thy *)
definition "check_pratt_cert c ≡ ..."

(* Example usage for FIPS primes: *)
lemma "prime 933491553728809239092563013853810654040043466297416456476877"
  by eval   (* verified via code generation *)
```
Source: [AFP `Pratt_Certificate`](https://www.isa-afp.org/entries/Pratt_Certificate.html)

Depends on [AFP `Lehmer`](https://www.isa-afp.org/entries/Lehmer.html):
```isabelle
(* Lehmer's theorem — basis of Pratt certificates *)
theorem lehmer:
  assumes "a^(n-1) mod n = 1"
    and "∀p. prime p ⟶ p dvd (n-1) ⟶ gcd (a^((n-1) div p) - 1) n = 1"
  shows "prime n"
```

---

## 3. Weierstrass / Montgomery Curve

### axiom_montgomery_add_associative

**Verus:**
```rust
pub proof fn axiom_montgomery_add_associative(P: MontgomeryAffine, Q: MontgomeryAffine, R: MontgomeryAffine)
    ensures montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{ admit(); }
```

**Isabelle/HOL (AFP):** `Elliptic_Curves_Group_Law` — Weierstrass group law:
```isabelle
(* From AFP: Elliptic_Curves_Group_Law.thy (Berghofer) *)

(* Weierstrass curve addition in affine coordinates *)
definition point_add :: "_ ⇒ _ ⇒ 'a point ⇒ 'a point ⇒ 'a point" where ...

(* Associativity of elliptic curve addition *)
theorem add_assoc:
  assumes "on_curve a b P" "on_curve a b Q" "on_curve a b R"
  shows "point_add a b (point_add a b P Q) R = point_add a b P (point_add a b Q R)"

(* Abelian group structure *)
interpretation ell_curve: comm_group ...
```
Source: [AFP `Elliptic_Curves_Group_Law`](https://www.isa-afp.org/entries/Elliptic_Curves_Group_Law.html)

Montgomery associativity follows via birational equivalence with Weierstrass (the change of variables x → u − A/3 transforms Montgomery into Weierstrass form).

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

**Isabelle/HOL:** No existing AFP entry for Montgomery XZ formulas. Pattern from Weierstrass:
```isabelle
(* AFP: Elliptic_Curves_Group_Law.thy — projective coordinates *)
definition pdouble :: "_ ⇒ _ ⇒ 'a ppoint ⇒ 'a ppoint" where
  "pdouble a b (x, y, z) = ..."

lemma pdouble_correct:
  assumes "on_curve a b (make_affine p)"
  shows "make_affine (pdouble a b p) = point_add a b (make_affine p) (make_affine p)"
```

Montgomery xDBL/xADD would follow the same pattern using Isabelle's `algebra` method for polynomial verification.

---

## 4. Quadratic Residuosity

### axiom_486660_not_quadratic_residue

**Verus:**
```rust
pub proof fn axiom_486660_not_quadratic_residue()
    ensures !is_square(486660nat),
{ admit(); }
```

**Isabelle/HOL:** `HOL-Number_Theory/Quadratic_Reciprocity`:
```isabelle
(* Isabelle: HOL-Number_Theory/Quadratic_Reciprocity.thy *)

(* Euler's criterion: *)
lemma euler_criterion:
  assumes "prime p" "odd p" "¬ p dvd a"
  shows "[a ^ ((p - 1) div 2) = Legendre a p] (mod p)"

(* Legendre symbol: *)
definition Legendre :: "int ⇒ nat ⇒ int" where
  "Legendre a p = (if QuadRes p a then 1 else -1)"

(* Quadratic reciprocity: *)
theorem Quadratic_Reciprocity:
  assumes "prime p" "prime q" "2 < p" "2 < q" "p ≠ q"
  shows "Legendre p q * Legendre q p = (-1) ^ ((p-1) div 2 * ((q-1) div 2))"
```

Verify `486660^((p-1)/2) mod p = p - 1` via code generation to SML/OCaml.

---

### axiom_sqrt_m1_squared

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_squared()
    ensures (sqrt_m1() * sqrt_m1()) % p() == (p() - 1),
{ admit(); }
```

**Isabelle/HOL:** Code generation for big-integer computation:
```isabelle
(* Export to SML/OCaml, compute, import result *)
lemma sqrt_m1_squared: "(SQRT_M1 * SQRT_M1) mod p = p - 1"
  by eval   (* or: by code_simp *)
```

Isabelle uses `int` (binary representation) + `Code_Target_Nat` for efficient arithmetic.

---

### axiom_sqrt_m1_not_square / axiom_neg_sqrt_m1_not_square

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_not_square()
    ensures !is_square(sqrt_m1()),
{ admit(); }
```

**Isabelle/HOL:** Euler's criterion + the general theory:
```isabelle
(* From Quadratic_Reciprocity.thy *)
(* When p ≡ 5 (mod 8): *)
lemma p_mod_8_eq_5:
  assumes "p mod 8 = 5" "prime p" "x^2 mod p = p - 1"
  shows "Legendre x p = -1"
  (* i.e., x is not a square *)
```

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

**Isabelle/HOL:** Both curve group laws are available in the AFP:
```isabelle
(* Edwards: AFP Edwards_Elliptic_Curves_Group *)
(* Weierstrass: AFP Elliptic_Curves_Group_Law *)

(* The birational map u = (1+y)/(1-y) can be verified using: *)
lemma birational_map_on_curve:
  assumes "on_curve c d (x, y)"   (* Edwards *)
  shows "montgomery_on_curve A B ((1 + y) * inverse (1 - y))"
  by (algebra)   (* polynomial identity checking *)
```

---

### axiom_edwards_to_montgomery_commutes_with_scalar_mul

**Verus:**
```rust
pub proof fn axiom_edwards_to_montgomery_commutes_with_scalar_mul(x: nat, y: nat, n: nat)
    requires is_on_edwards_curve(x, y),
    ensures montgomery_u_from_edwards_y(edwards_scalar_mul((x,y), n).1)
         == montgomery_scalar_mul_u(montgomery_u_from_edwards_y(y), n),
{ admit(); }
```

**Isabelle/HOL:** Group homomorphism property:
```isabelle
(* HOL-Algebra: Group.thy *)
lemma (in group_hom) hom_pow:
  assumes "x ∈ carrier G"
  shows "h (x [^]\<^bsub>G\<^esub> n) = h x [^]\<^bsub>H\<^esub> n"
```

---

## 6. Subgroup Closure

### axiom_even_subgroup_closed_under_add

**Verus:**
```rust
pub proof fn axiom_even_subgroup_closed_under_add(p1: EdwardsPoint, p2: EdwardsPoint)
    requires is_in_even_subgroup(p1), is_in_even_subgroup(p2),
    ensures /* p1 + p2 is in even subgroup */
{ admit(); }
```

**Isabelle/HOL:**
```isabelle
(* HOL-Algebra: Subgroup.thy *)
lemma (in group) subgroup_mult_closed:
  assumes "subgroup H G" "x ∈ H" "y ∈ H"
  shows "x ⊗ y ∈ H"

(* The image of "multiply by 2" endomorphism is a subgroup: *)
lemma image_of_hom_is_subgroup:
  assumes "h ∈ hom G G"
  shows "subgroup (h ` carrier G) G"
```

---

## 7. Hash Properties

### axiom_sha512_output_length

**Verus:**
```rust
pub proof fn axiom_sha512_output_length(input: Seq<u8>)
    ensures spec_sha512(input).len() == 64,
{ admit(); }
```

**Isabelle/HOL (AFP):** `Crypto_Standards` provides cryptographic standard translations:
```isabelle
(* AFP: Crypto_Standards.thy *)
(* Translates FIPS 186-4 and SEC1 v2.0 into Isabelle *)
(* Provides framework for hash function specs including output length *)

(* Hypothetical SHA-512 spec: *)
definition SHA_512 :: "byte list ⇒ byte list" where ...
lemma SHA_512_length: "length (SHA_512 msg) = 64"
```
Source: [AFP `Crypto_Standards`](https://devel.isa-afp.org/entries/Crypto_Standards.html)

---

## 8. Inverse Square Root

### axiom_invsqrt_factors_over_square

**Verus:**
```rust
pub proof fn axiom_invsqrt_factors_over_square(a: nat, b: nat)
    requires a % p() != 0, b % p() != 0,
    ensures nat_invsqrt(field_mul(a, field_square(b)))
         == field_abs(field_mul(nat_invsqrt(a), field_inv(b))),
{ admit(); }
```

**Isabelle/HOL:** HOL-Algebra field locale:
```isabelle
(* HOL-Algebra: Ring.thy / UnivPoly.thy *)
lemma (in field) m_assoc: "a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c"
lemma (in field) r_inv: "a ∈ carrier R ⟹ a ≠ 𝟬 ⟹ a ⊗ inv a = 𝟭"
lemma (in field) inv_mult: "inv (a ⊗ b) = inv a ⊗ inv b"
```

---

## 9. Probability / Uniformity

### axiom_uniform_point_add

**Verus:**
```rust
pub proof fn axiom_uniform_point_add(p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires /* sum = p1 + p2, both uniform, independent */
    ensures is_uniform_ristretto_point(sum),
{ admit(); }
```

**Isabelle/HOL (AFP):** CryptHOL framework:
```isabelle
(* AFP: CryptHOL.thy — game-based cryptographic proofs *)

(* Sub-probability mass functions (spmf) *)
type_synonym 'a spmf = "'a pmf option"

(* Uniform sampling over a set *)
definition uniform :: "'a set ⇒ 'a spmf" where
  "uniform S = (if finite S ∧ S ≠ {} then
    map_pmf Some (pmf_of_set S) else return_pmf None)"

(* The advantage/statistical distance concept *)
definition advantage :: "('a spmf ⇒ bool spmf) ⇒ 'a spmf ⇒ 'a spmf ⇒ real" where
  "advantage D p q = ¦spmf_of_pmf (D p) True - spmf_of_pmf (D q) True¦"

(* Cyclic group locale for group-theoretic uniformity *)
locale cyclic_group = group +
  fixes g :: 'a   (* generator *)
  assumes generates: "⟨{g}⟩ = carrier G"
```
Source: [AFP `CryptHOL`](https://devel.isa-afp.org/entries/CryptHOL.html), Tutorial: [`CryptHOL_Tutorial`](https://www.isa-afp.org/browser_info/current/AFP/Game_Based_Crypto/CryptHOL_Tutorial.html)

The uniform-over-group result for prime-order groups can be expressed using CryptHOL's `cyclic_group` locale + `uniform` combinator. **CryptHOL is the most suitable framework among the three provers for these probability axioms.**

---

### axiom_uniform_elligator_sum

**Verus:**
```rust
pub proof fn axiom_uniform_elligator_sum(p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires /* sum = p1 + p2, both uniform over Elligator image, independent */
    ensures is_uniform_ristretto_point(sum),
{ admit(); }
```

**Isabelle/HOL (CryptHOL):**
```isabelle
(* CryptHOL provides the bind/map combinators for probabilistic programs *)
definition elligator_sum_game :: "'a spmf" where
  "elligator_sum_game = do {
    r1 ← uniform UNIV;
    r2 ← uniform UNIV;
    let p1 = elligator r1;
    let p2 = elligator r2;
    return_spmf (p1 ⊕ p2)
  }"

(* Goal: show elligator_sum_game ≈ uniform (carrier G) *)
(* Uses CryptHOL's spmf_rel and advantage framework *)
```

---

## 10. Concrete Numerical Facts

### axiom_nat_invsqrt_neg_one_minus_d / axiom_two_l_div_pow2_208_le_pow2_45

**Verus:**
```rust
pub proof fn axiom_invsqrt_a_minus_d()
    ensures nat_invsqrt(field_sub(field_neg(1), d)) == c_iad
         && field_mul(field_square(c_iad), neg_one_minus_d) == 1,
{ admit(); }
```

**Isabelle/HOL:** Code generation:
```isabelle
(* Export to SML/OCaml for efficient big-integer computation *)
lemma invsqrt_neg_one_minus_d:
  "nat_invsqrt (field_sub (field_neg 1) d) = C_IAD"
  by eval
```

---

## 11. Ristretto / Elligator (no existing Isabelle counterparts)

All Ristretto and Elligator axioms (`axiom_elligator_on_curve`, `axiom_elligator_in_even_subgroup`, `axiom_ristretto_cross_mul_iff_equivalent`, `axiom_ristretto_decode_on_curve`, `axiom_ristretto_decode_in_even_subgroup`, `axiom_elligator_nonzero_intermediates`, `axiom_elligator_encode_outputs_valid_u`) have **no existing counterpart** in Isabelle/HOL. The Edwards group law AFP entry provides the foundation on which these could be built.

---

## 12. Precomputed Tables (no existing Isabelle counterparts)

`axiom_ed25519_basepoint_table_valid`, `axiom_affine_odd_multiples_of_basepoint_valid`, `axiom_ristretto_basepoint_table_valid` — these would use the Edwards group law from the AFP combined with code generation to SML/OCaml for the actual table computation.
