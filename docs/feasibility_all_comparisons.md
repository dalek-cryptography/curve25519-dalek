# Verus Axioms vs. Lean / Rocq / Isabelle: Unified Comparison

For each Verus axiom that has an existing correspondent (or closely related theorem)
in at least one of Lean 4, Rocq (Coq), or Isabelle/HOL, this document shows:

1. The mathematical statement in textbook notation
2. The Verus definition
3. All matching theorems across the three provers

Axioms with **no correspondent in any prover** are collected in [Section 10](#10-axioms-with-no-existing-correspondent-in-any-prover).

Legend: **direct** = the prover has a machine-checked proof of (essentially) the same statement. **framework** = the prover has the algebraic/logical infrastructure but the specific statement must still be instantiated or proved.

See also the per-prover files:
[feasibility_lean_comparisons.md](feasibility_lean_comparisons.md) |
[feasibility_rocq_comparisons.md](feasibility_rocq_comparisons.md) |
[feasibility_isabelle_comparisons.md](feasibility_isabelle_comparisons.md)

---

## 1. Primality

### 1.1 axiom_p_is_prime

$$
p = 2^{255} - 19 \;\;\text{is prime}
$$

The field modulus p = 2²⁵⁵ − 19 is prime. This underpins every field-theoretic property (existence of inverses, Fermat's little theorem, etc.).

**Verus:**
```rust
pub proof fn axiom_p_is_prime()
    ensures is_prime(p()),
{ admit(); }
```

**Lean 4** (framework) -- `Mathlib.NumberTheory.LucasPrimality`:
```lean
theorem lucas_primality (p : ℕ) (a : ZMod p)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ q, Nat.Prime q → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) :
    Nat.Prime p
```
Supply a witness `a` and the full factorisation of `p − 1`, verify exponentiations via `native_decide`.

**Rocq** (framework) -- [CoqPrime](https://thery.gitlabpages.inria.fr/coqprime/), `Pocklington.v`:
```coq
Theorem Pocklington :
  forall N F1 R1,
    N - 1 = F1 * R1 ->  Z.gcd F1 R1 = 1 ->  1 < F1 ->
    (forall p, prime p -> (p | F1) ->
      exists a, 1 < a /\ a^(N-1) mod N = 1 /\ Z.gcd (a^((N-1)/p) - 1) N = 1) ->
    (forall p, prime p -> (p | N) -> N <= p * p \/ R1 < p) ->
    prime N.
```
Pipeline: `primo` → `o2v` → `v2v` → `coqc`. Verified Mersenne primes up to M₂₂₈₁ in ~2.4 s.

**Isabelle/HOL** (framework) -- [AFP `Pratt_Certificate`](https://www.isa-afp.org/entries/Pratt_Certificate.html):
```isabelle
theorem pratt_sound:
  assumes "valid_cert (Prime p)"
  shows "prime p"
```
Certificate checking via code generation to SML/OCaml. Depends on [AFP `Lehmer`](https://www.isa-afp.org/entries/Lehmer.html).

---

### 1.2 axiom_group_order_is_prime

$$
L = 2^{252} + 27742317777372353535851937790883648493 \;\;\text{is prime}
$$

The Ed25519/Ristretto group order L is prime.

**Verus:**
```rust
pub proof fn axiom_group_order_is_prime()
    ensures is_prime(group_order()),
{ admit(); }
```

**Lean 4 / Rocq / Isabelle:** Same three frameworks as Section 1.1, applied to L instead of p.

---

## 2. Edwards Curve Group Law

The twisted Edwards curve for Ed25519 is:

$$
-x^2 + y^2 = 1 + d\,x^2 y^2 \pmod{p}
$$

where d = −121665/121666 (mod p). Addition is defined by:

$$
(x_1, y_1) +_E (x_2, y_2) = \left(\frac{x_1 y_2 + y_1 x_2}{1 + d\,x_1 x_2 y_1 y_2},\;\frac{y_1 y_2 + x_1 x_2}{1 - d\,x_1 x_2 y_1 y_2}\right)
$$

### 2.1 axiom_edwards_add_associative

$$
(P_1 +_E P_2) +_E P_3 \;=\; P_1 +_E (P_2 +_E P_3)
$$

Edwards addition is associative (for all points, not just those on a specific curve instance).

**Verus:**
```rust
pub proof fn axiom_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
    ensures
        edwards_add(edwards_add(x1,y1,x2,y2).0, edwards_add(x1,y1,x2,y2).1, x3, y3)
        == edwards_add(x1, y1, edwards_add(x2,y2,x3,y3).0, edwards_add(x2,y2,x3,y3).1),
{ admit(); }
```

**Isabelle/HOL** (**direct**) -- [AFP `Edwards_Elliptic_Curves_Group`](https://devel.isa-afp.org/entries/Edwards_Elliptic_Curves_Group.html) (Hales & Raya, IJCAR 2020):
```isabelle
definition add :: "'a ⇒ 'a ⇒ 'a × 'a ⇒ 'a × 'a ⇒ 'a × 'a" where
  "add c d (x1, y1) (x2, y2) =
    ((x1*y2 + y1*x2) / (1 + d*x1*x2*y1*y2),
     (y1*y2 - c*x1*x2) / (1 - d*x1*x2*y1*y2))"

theorem associativity:
  assumes "on_curve c d P" "on_curve c d Q" "on_curve c d R"
  shows "add c d (add c d P Q) R = add c d P (add c d Q R)"
```
Specialise with c = −1, d = −121665/121666 for Ed25519.

**Lean 4** (framework) -- [`Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.html):
```lean
instance WeierstrassCurve.Jacobian.Point.instAddCommGroup :
    AddCommGroup (WeierstrassCurve.Jacobian.Point W) := ...
```
Weierstrass only. No Edwards curve definition in Mathlib; would need new formalisation or birational equivalence.

**Rocq** (framework) -- [Fiat-Crypto `src/Curves/Edwards/`](https://github.com/mit-plv/fiat-crypto/tree/master/src/Curves/Edwards) contains Edwards curve definitions. Full associativity proof via Hales-Raya polynomial identity method:
```coq
Lemma edwards_add_assoc : forall x1 y1 x2 y2 x3 y3,
    let p12 := edwards_add x1 y1 x2 y2 in
    let p23 := edwards_add x2 y2 x3 y3 in
    edwards_add (fst p12) (snd p12) x3 y3 =
    edwards_add x1 y1 (fst p23) (snd p23).
```

---

### 2.2 axiom_edwards_add_complete

$$
\forall\, (x_1, y_1),\, (x_2, y_2) \;\text{on curve}:\quad
1 + d\,x_1 x_2 y_1 y_2 \neq 0 \;\;\wedge\;\; 1 - d\,x_1 x_2 y_1 y_2 \neq 0
$$

and the result is again on the curve. Completeness holds because d is not a square in GF(p).

**Verus:**
```rust
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires is_on_edwards_curve(x1, y1), is_on_edwards_curve(x2, y2),
    ensures
        field_add(1, t) != 0 && field_sub(1, t) != 0,
        is_on_edwards_curve(edwards_add(x1, y1, x2, y2).0, edwards_add(x1, y1, x2, y2).1),
{ admit(); }
```

**Isabelle/HOL** (**direct**) -- same AFP entry:
```isabelle
lemma add_closure:
  assumes "on_curve c d P" "on_curve c d Q" and "¬ is_square d"
  shows "on_curve c d (add c d P Q)"
    and "1 + d * fst P * fst Q * snd P * snd Q ≠ 0"
    and "1 - d * fst P * fst Q * snd P * snd Q ≠ 0"
```

**Lean 4** (framework) -- Weierstrass analogue only:
```lean
theorem WeierstrassCurve.Jacobian.nonsingular_add {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) : W.Nonsingular (W.add P Q)
```

**Rocq** (framework) -- MathComp finite field infrastructure for the non-square argument:
```coq
(* d is not a square ⟹ d·x² ≠ 1 *)
Lemma nonsquare_neq_square (F : fieldType) (d x : F) :
    ~~ is_square d -> d * x ^+ 2 <> 1.
```

---

### 2.3 axiom_edwards_scalar_mul_signed_additive

$$
[a]P +_E [b]P = [a + b]P \qquad (a, b \in \mathbb{Z})
$$

Signed scalar multiplication is additive (group homomorphism property of the scalar map).

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures
        edwards_add(edwards_scalar_mul_signed(P, a), edwards_scalar_mul_signed(P, b))
        == edwards_scalar_mul_signed(P, a + b),
{ admit(); }
```

**Lean 4** (framework) -- [`Mathlib.Algebra.Group.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html):
```lean
theorem add_zsmul {G : Type} [AddCommGroup G] (a b : ℤ) (g : G) :
    (a + b) • g = a • g + b • g
```

**Rocq** (framework) -- MathComp `ssrint.v`:
```coq
Lemma mulrzDl (R : zmodType) (x : R) (m n : int) :
    x *~ (m + n) = x *~ m + x *~ n.
```

**Isabelle/HOL** (framework) -- `HOL-Algebra/Group.thy`:
```isabelle
lemma (in group) int_pow_mult:
  "x [^] (m + n :: int) = x [^] m ⊗ x [^] n"
```

---

### 2.4 axiom_edwards_scalar_mul_distributive

$$
[n](P +_E Q) = [n]P +_E [n]Q
$$

Scalar multiplication distributes over addition (the "multiply by n" endomorphism is a group homomorphism in any abelian group).

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_distributive(a: (nat, nat), b: (nat, nat), n: nat)
    ensures
        edwards_scalar_mul(edwards_add(a.0, a.1, b.0, b.1), n)
        == edwards_add(edwards_scalar_mul(a, n).0, edwards_scalar_mul(a, n).1,
                       edwards_scalar_mul(b, n).0, edwards_scalar_mul(b, n).1),
{ admit(); }
```

**Lean 4** (framework) -- [`Mathlib.Algebra.Group.Hom.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html):
```lean
theorem AddMonoidHom.map_add {G H : Type} [AddCommMonoid G] [AddCommMonoid H]
    (f : G →+ H) (a b : G) : f (a + b) = f a + f b
```

**Rocq** (framework) -- MathComp `fingroup.v`:
```coq
Lemma expgD (G : finGroupType) (x : G) (m n : nat) :
    x ^+ (m + n) = x ^+ m * x ^+ n.
```

**Isabelle/HOL** (framework) -- `HOL-Algebra/Group.thy`:
```isabelle
lemma (in comm_group) hom_mult:
  assumes "h ∈ hom G G" "x ∈ carrier G" "y ∈ carrier G"
  shows "h (x ⊗ y) = h x ⊗ h y"
```

---

## 3. Montgomery Curve

The Montgomery curve for Curve25519 is:

$$
v^2 = u^3 + 486662\,u^2 + u \pmod{p}
$$

The Montgomery ladder uses projective X : Z coordinates where u = X/Z.

### 3.1 axiom_montgomery_add_associative

$$
(P +_M Q) +_M R = P +_M (Q +_M R)
$$

**Verus:**
```rust
pub proof fn axiom_montgomery_add_associative(
    P: MontgomeryAffine, Q: MontgomeryAffine, R: MontgomeryAffine)
    ensures montgomery_add(montgomery_add(P, Q), R) == montgomery_add(P, montgomery_add(Q, R)),
{ admit(); }
```

**Isabelle/HOL** (framework) -- [AFP `Elliptic_Curves_Group_Law`](https://www.isa-afp.org/entries/Elliptic_Curves_Group_Law.html) (Weierstrass form):
```isabelle
theorem add_assoc:
  assumes "on_curve a b P" "on_curve a b Q" "on_curve a b R"
  shows "point_add a b (point_add a b P Q) R = point_add a b P (point_add a b Q R)"

interpretation ell_curve: comm_group ...
```
Montgomery associativity follows via the standard change of variables u → x − A/3 which transforms Montgomery into Weierstrass form.

**Lean 4** (framework) -- same Weierstrass `instAddCommGroup` as Section 2.1.

**Rocq** -- Fiat-Crypto has Montgomery definitions but relies on the Weierstrass group law proof for associativity.

---

### 3.2 axiom_xdbl_projective_correct

$$
\text{xDBL}(U : W) = (U' : W') \quad\text{representing}\quad [2]P
$$

If (U : W) represents the affine Montgomery point P, then `xDBL(U, W)` represents 2P.

**Verus:**
```rust
pub proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires projective_represents_montgomery_or_infinity_nat(U, W, P),
    ensures projective_represents_montgomery_or_infinity_nat(
        spec_xdbl_projective(U, W).0, spec_xdbl_projective(U, W).1,
        montgomery_add(P, P)),
{ admit(); }
```

**Rocq** (**direct**) -- [Fiat-Crypto `src/Curves/Montgomery/XZProofs.v`](https://github.com/mit-plv/fiat-crypto/blob/master/src/Curves/Montgomery/XZProofs.v):
```coq
Lemma xzladderstep_correct
  (a24 : F) (X1 : F) (P Q : point)
  (HX1 : X1 = to_xz P - to_xz Q)
  :
  let '(x2, z2, x3, z3) := xzladderstep a24 X1 (to_xz P) 1 (to_xz Q) 1 in
  (* x2/z2 represents 2*P, x3/z3 represents P+Q *)
  ...
```
Production code deployed in BoringSSL and the Linux kernel. **This is the closest existing mechanised proof of the axiom in any prover.**

**Isabelle/HOL** (framework) -- Weierstrass projective pattern from `Elliptic_Curves_Group_Law`:
```isabelle
lemma pdouble_correct:
  assumes "on_curve a b (make_affine p)"
  shows "make_affine (pdouble a b p) = point_add a b (make_affine p) (make_affine p)"
```

**Lean 4** -- No existing theorem. Weierstrass Jacobian doubling formulas exist in `Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula`.

---

### 3.3 axiom_xadd_projective_correct

$$
\text{xADD}(U_P : W_P,\; U_Q : W_Q,\; u_{P-Q}) = (U_{P+Q} : W_{P+Q})
$$

Differential addition: given projective representations of P, Q and the affine u-coordinate of P − Q, compute P + Q.

**Verus:**
```rust
pub proof fn axiom_xadd_projective_correct(
    P: MontgomeryAffine, Q: MontgomeryAffine,
    U_P: nat, W_P: nat, U_Q: nat, W_Q: nat, affine_PmQ: nat)
    requires
        projective_represents_montgomery_or_infinity_nat(U_P, W_P, P),
        projective_represents_montgomery_or_infinity_nat(U_Q, W_Q, Q),
        P != Q,  affine_PmQ != 0,
    ensures projective_represents_montgomery_or_infinity_nat(
        spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ).0,
        spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ).1,
        montgomery_add(P, Q)),
{ admit(); }
```

**Rocq** (**direct**) -- Same `xzladderstep_correct` from Fiat-Crypto (computes both xDBL and xADD in one ladder step).

**Isabelle/HOL** (framework) -- same Weierstrass projective pattern. **Lean 4** -- no existing theorem.

---

## 4. Quadratic Residuosity & Square Roots

### 4.1 axiom_486660_not_quadratic_residue

$$
\left(\frac{486660}{p}\right) = -1
$$

486660 (= A − 2 where A = 486662) is not a quadratic residue mod p.

**Verus:**
```rust
pub proof fn axiom_486660_not_quadratic_residue()
    ensures !is_square(486660nat),
{ admit(); }
```

**Lean 4** (framework) -- [`Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.html):
```lean
theorem quadraticChar_neg_one_iff_not_isSquare {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {a : F} :
    (quadraticChar F) a = -1 ↔ ¬ IsSquare a
```
Combined with Euler's criterion. Instantiate F = ZMod p, verify `486660^((p−1)/2) mod p = p − 1` via `native_decide`.

**Rocq** (framework) -- MathComp `finfield.v` / Euler's criterion over `ZModp`:
```coq
Eval vm_compute in (486660 ^ ((p - 1) / 2) mod p).
(* Result = p - 1, hence Legendre symbol = -1 *)
```

**Isabelle/HOL** (framework) -- `HOL-Number_Theory/Quadratic_Reciprocity.thy`:
```isabelle
lemma euler_criterion:
  assumes "prime p" "odd p" "¬ p dvd a"
  shows "[a ^ ((p - 1) div 2) = Legendre a p] (mod p)"
```
Verify via code generation to SML/OCaml.

---

### 4.2 axiom_2_times_486661_not_qr

$$
\left(\frac{2 \cdot 486661}{p}\right) = -1
$$

Since p ≡ 5 (mod 8), 2 is a non-QR; 486661 is a QR; their product is a non-QR.

**Verus:**
```rust
pub proof fn axiom_2_times_486661_not_qr()
    ensures !is_square((2nat * 486661nat) % p()),
{ admit(); }
```

**All three provers:** Same Euler-criterion / Legendre-symbol frameworks as Section 4.1.

---

### 4.3 axiom_sqrt_m1_squared

$$
i^2 \equiv -1 \pmod{p}
$$

where i = SQRT_M1 is a specific ~252-bit constant.

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_squared()
    ensures (sqrt_m1() * sqrt_m1()) % p() == (p() - 1),
{ admit(); }
```

**Lean 4** (framework) -- direct computation over `ZMod p`:
```lean
example : ((SQRT_M1 : ZMod p) ^ 2 = -1) := by native_decide
```
Source: [`Mathlib.Data.ZMod.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html)

**Rocq** (framework) -- big-integer computation:
```coq
Lemma sqrt_m1_squared : (SQRT_M1 * SQRT_M1) mod p = p - 1.
Proof. native_compute. reflexivity. Qed.
```

**Isabelle/HOL** (framework) -- code generation:
```isabelle
lemma sqrt_m1_squared: "(SQRT_M1 * SQRT_M1) mod p = p - 1"
  by eval
```

---

### 4.4 axiom_sqrt_m1_not_square / axiom_neg_sqrt_m1_not_square

$$
\left(\frac{i}{p}\right) = -1 \qquad\text{and}\qquad \left(\frac{-i}{p}\right) = -1
$$

Neither i = sqrt(−1) nor −i is a square in GF(p). Follows from p ≡ 5 (mod 8) and Euler's criterion.

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_not_square()
    ensures !is_square(sqrt_m1()),
{ admit(); }

pub proof fn axiom_neg_sqrt_m1_not_square()
    ensures !is_square((p() - sqrt_m1()) as nat),
{ admit(); }
```

**Lean 4** (framework) -- [`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html):
```lean
theorem ZMod.exists_sq_eq_neg_one_iff {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    (∃ y : ZMod p, y ^ 2 = -1) ↔ p % 4 ≠ 3
```

**Rocq** (framework) -- MathComp Euler criterion over `ZModp`.

**Isabelle/HOL** (framework) -- `Quadratic_Reciprocity.thy`:
```isabelle
(* When p ≡ 5 (mod 8) and x² ≡ −1 (mod p): *)
lemma p_mod_8_eq_5:
  assumes "p mod 8 = 5" "prime p" "x^2 mod p = p - 1"
  shows "Legendre x p = -1"
```

---

## 5. Birational Equivalence (Edwards ↔ Montgomery)

The birational map from Edwards to Montgomery is:

$$
u = \frac{1 + y}{1 - y}, \qquad y = \frac{u - 1}{u + 1}
$$

### 5.1 axiom_edwards_to_montgomery_preserves_validity

$$
(x, y) \in E \;\implies\; u = \frac{1+y}{1-y} \;\text{is a valid Montgomery u-coordinate}
$$

**Verus:**
```rust
pub proof fn axiom_edwards_to_montgomery_preserves_validity(x: nat, y: nat)
    requires is_on_edwards_curve(x, y),
    ensures is_valid_u_coordinate(montgomery_u_from_edwards_y(y)),
{ admit(); }
```

**Isabelle/HOL** (framework) -- AFP has both Edwards and Weierstrass group laws:
```isabelle
lemma birational_map_on_curve:
  assumes "on_curve c d (x, y)"
  shows "montgomery_on_curve A B ((1 + y) * inverse (1 - y))"
  by (algebra)
```

**Rocq** (framework) -- [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) has both Edwards and Montgomery curve definitions; the map u = (1+y)/(1−y) can be verified with `ring`.

**Lean 4** (framework) -- [`Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.html) provides isomorphism infrastructure for Weierstrass curves. The Edwards → Montgomery map needs custom definition.

---

### 5.2 axiom_montgomery_valid_u_implies_edwards_y_valid

$$
u \;\text{valid Montgomery coordinate},\; u \neq -1 \;\implies\; y = \frac{u-1}{u+1} \;\text{is valid Edwards}
$$

**Verus:**
```rust
pub proof fn axiom_montgomery_valid_u_implies_edwards_y_valid(u: nat)
    requires is_valid_u_coordinate(u), u != field_sub(0, 1),
    ensures is_valid_edwards_y_coordinate(edwards_y_from_montgomery_u(u)),
{ admit(); }
```

**All three provers:** Same birational-equivalence frameworks as Section 5.1, in the reverse direction.

---

### 5.3 axiom_edwards_to_montgomery_commutes_with_scalar_mul

$$
\varphi([n]P_{\text{Ed}}) = [n]\,\varphi(P_{\text{Ed}})
$$

where φ is the Edwards → Montgomery map. The birational map is a group homomorphism, so it commutes with scalar multiplication.

**Verus:**
```rust
pub proof fn axiom_edwards_to_montgomery_commutes_with_scalar_mul(x: nat, y: nat, n: nat)
    requires is_on_edwards_curve(x, y),
    ensures
        montgomery_u_from_edwards_y(edwards_scalar_mul((x, y), n).1)
        == montgomery_scalar_mul_u(montgomery_u_from_edwards_y(y), n),
{ admit(); }
```

**Lean 4** (framework) -- [`Mathlib.Algebra.Group.Hom.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html):
```lean
theorem AddMonoidHom.map_nsmul {M N : Type} [AddMonoid M] [AddMonoid N]
    (f : M →+ N) (n : ℕ) (a : M) : f (n • a) = n • f a
```

**Rocq** (framework) -- MathComp `morphism.v`:
```coq
Lemma morphim_expg (aT rT : finGroupType) (f : {morphism aT >-> rT})
    (x : aT) (n : nat) : f (x ^+ n) = (f x) ^+ n.
```

**Isabelle/HOL** (framework) -- `HOL-Algebra/Group.thy`:
```isabelle
lemma (in group_hom) hom_pow:
  assumes "x ∈ carrier G"
  shows "h (x [^]\<^bsub>G\<^esub> n) = h x [^]\<^bsub>H\<^esub> n"
```

---

## 6. Subgroup Closure

### 6.1 axiom_even_subgroup_closed_under_add

$$
P, Q \in 2E \;\implies\; P +_E Q \in 2E
$$

The even subgroup (image of the "doubling" endomorphism) is closed under addition. This is immediate from group theory: 2Q₁ + 2Q₂ = 2(Q₁ + Q₂).

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

**Lean 4** (framework) -- [`Mathlib.Algebra.Group.Subgroup.Defs`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Defs.html):
```lean
theorem AddSubgroup.add_mem {G : Type} [AddGroup G] {H : AddSubgroup G}
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a + b ∈ H
```

**Rocq** (framework) -- MathComp `fingroup.v`:
```coq
Lemma groupM (G : finGroupType) (H : {group G}) (x y : G) :
    x \in H -> y \in H -> x * y \in H.
```

**Isabelle/HOL** (framework) -- `HOL-Algebra/Subgroup.thy`:
```isabelle
lemma (in group) subgroup_mult_closed:
  assumes "subgroup H G" "x ∈ H" "y ∈ H"
  shows "x ⊗ y ∈ H"
```

---

## 7. Inverse Square Root

### 7.1 axiom_invsqrt_factors_over_square

$$
\text{invsqrt}(a \cdot b^2) = \left|\,\text{invsqrt}(a) \cdot b^{-1}\right|
$$

For nonzero a, b ∈ GF(p), the inverse square root factors over perfect squares.

**Verus:**
```rust
pub proof fn axiom_invsqrt_factors_over_square(a: nat, b: nat)
    requires a % p() != 0, b % p() != 0,
    ensures nat_invsqrt(field_mul(a, field_square(b)))
         == field_abs(field_mul(nat_invsqrt(a), field_inv(b))),
{ admit(); }
```

**Lean 4** (framework) -- field algebra from [`Mathlib.Algebra.Group.Even`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Even.html):
```lean
theorem mul_inv_cancel₀ {α : Type} [GroupWithZero α] {a : α} (ha : a ≠ 0) : a * a⁻¹ = 1
def IsSquare {α : Type} [Mul α] (a : α) : Prop := ∃ r, a = r * r
```

**Rocq** (framework) -- MathComp `GRing.Theory`:
```coq
Lemma mulVr (F : fieldType) (x : F) : x != 0 -> x^-1 * x = 1.
Lemma sqr_inv (F : fieldType) (x : F) : (x^-1)^+2 = (x^+2)^-1.
```

**Isabelle/HOL** (framework) -- `HOL-Algebra/Ring.thy`:
```isabelle
lemma (in field) r_inv: "a ∈ carrier R ⟹ a ≠ 𝟬 ⟹ a ⊗ inv a = 𝟭"
lemma (in field) inv_mult: "inv (a ⊗ b) = inv a ⊗ inv b"
```

---

### 7.2 axiom_invsqrt_a_minus_d

$$
\text{invsqrt}(-1 - d)^2 \cdot (-1 - d) = 1
$$

The constant INVSQRT_A_MINUS_D is the canonical inverse square root of (−1 − d), and (−1 − d) is a quadratic residue (so the product is 1, not i).

**Verus:**
```rust
pub proof fn axiom_invsqrt_a_minus_d()
    ensures
        nat_invsqrt(neg_one_minus_d) == c_iad
        && field_mul(field_square(c_iad), neg_one_minus_d) == 1,
{ admit(); }
```

**Rocq** (framework) -- `native_compute` over Z:
```coq
Lemma invsqrt_a_minus_d : (C_IAD * C_IAD * NEG_ONE_MINUS_D) mod p = 1.
Proof. native_compute. reflexivity. Qed.
```

**Isabelle/HOL** (framework) -- code generation:
```isabelle
lemma invsqrt_neg_one_minus_d:
  "nat_invsqrt (field_sub (field_neg 1) d) = C_IAD"
  by eval
```

**Lean 4** -- `native_decide` over `ZMod p`.

---

## 8. Hash Properties

### 8.1 axiom_sha512_output_length

$$
\forall\, m:\quad |\text{SHA-512}(m)| = 64 \;\text{bytes}
$$

**Verus:**
```rust
pub proof fn axiom_sha512_output_length(input: Seq<u8>)
    ensures spec_sha512(input).len() == 64,
{ admit(); }
```

**Rocq** (framework) -- [VST SHA-256 verification](https://www.cs.princeton.edu/~appel/papers/verif-sha.pdf) (Appel, Princeton):
```coq
Definition SHA_256 (msg : list byte) : list byte := ...
Lemma SHA_256_length : forall msg, length (SHA_256 msg) = 32.
```
SHA-512 follows the same structure (Merkle-Damgard with 80 rounds of 64-bit words).

**Isabelle/HOL** (framework) -- [AFP `Crypto_Standards`](https://devel.isa-afp.org/entries/Crypto_Standards.html) translates FIPS standards into Isabelle; provides the framework for hash function specs.

**Lean 4** -- No SHA-512 spec. SHA-3 was formalised by Doussot (2024).

---

### 8.2 axiom_hash_is_canonical

$$
\text{fe}(P_1) = \text{fe}(P_2) \;\implies\; H(\ldots \| P_1) = H(\ldots \| P_2)
$$

Hashing depends only on the canonical field-element value, not the byte representation.

**Verus:**
```rust
pub proof fn axiom_hash_is_canonical<H>(point1: &MontgomeryPoint, point2: &MontgomeryPoint, state: H)
    requires field_element_from_bytes(&point1.0) == field_element_from_bytes(&point2.0),
    ensures spec_state_after_hash_montgomery(state, point1)
         == spec_state_after_hash_montgomery(state, point2),
{ admit(); }
```

**All three provers:** This is a consequence of the canonical-encoding property of field elements. In each prover it reduces to showing that the byte→field→byte round-trip is deterministic, which is straightforward once the field representation is formalised.

---

## 9. Probability and Uniformity

All probability axioms require a framework for discrete distributions, independence, and measure-preserving group actions. No prover has the specific theorems, but the infrastructure varies significantly.

### 9.1 axiom_uniform_bytes_split

$$
X \sim \text{Uniform}([0, 2^{512})) \;\implies\; X_{\text{lo}},\, X_{\text{hi}} \sim \text{Uniform}([0, 2^{256})) \;\;\text{and independent}
$$

Splitting 64 uniform bytes into two halves preserves uniformity and gives independence.

**Verus:**
```rust
pub proof fn axiom_uniform_bytes_split(bytes: &[u8; 64], first: &[u8; 32], second: &[u8; 32])
    requires first@ == bytes@.subrange(0, 32), second@ == bytes@.subrange(32, 64),
             is_uniform_bytes(bytes),
    ensures is_uniform_bytes(first), is_uniform_bytes(second),
            is_independent_uniform_bytes32(first, second),
{ admit(); }
```

**Isabelle/HOL** (best framework) -- [AFP `CryptHOL`](https://devel.isa-afp.org/entries/CryptHOL.html):
```isabelle
type_synonym 'a spmf = "'a pmf option"

definition uniform :: "'a set ⇒ 'a spmf" where
  "uniform S = (if finite S ∧ S ≠ {} then map_pmf Some (pmf_of_set S) else return_pmf None)"
```
CryptHOL's monadic `spmf` type supports `bind`, `map`, independence reasoning, and statistical distance.

**Lean 4** (framework) -- [`Mathlib.Probability.Distributions.Uniform`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Uniform.html):
```lean
def PMF.uniformOfFintype (α : Type) [Fintype α] [Nonempty α] : PMF α := ...
```

**Rocq** (framework) -- MathComp-Analysis `probability.v` / `measure.v`.

---

### 9.2 axiom_from_bytes_uniform

$$
X \sim \text{Uniform}([0, 2^{256})) \;\implies\; X \bmod 2^{255} \sim \text{Uniform}([0, 2^{255}))
$$

Clearing the high bit preserves uniformity (with cryptographically negligible bias ≈ 19/2²⁵⁵).

**Verus:**
```rust
pub proof fn axiom_from_bytes_uniform(bytes: &[u8; 32], fe: &FieldElement)
    requires fe51_as_nat(fe) == u8_32_as_nat(bytes) % pow2(255),
    ensures is_uniform_bytes(bytes) ==> is_uniform_field_element(fe),
{ assume(is_uniform_bytes(bytes) ==> is_uniform_field_element(fe)); }
```

**All three provers:** Same probability frameworks as 9.1. The modular-reduction bias argument is standard.

---

### 9.3 axiom_from_bytes_independent

Applying `from_bytes` to two independent byte strings yields independent field elements.

**Verus:**
```rust
pub proof fn axiom_from_bytes_independent(
    bytes1: &[u8; 32], bytes2: &[u8; 32], fe1: &FieldElement, fe2: &FieldElement)
    requires /* fe_i from bytes_i */, is_independent_uniform_bytes32(bytes1, bytes2),
    ensures is_independent_uniform_field_elements(fe1, fe2),
{ admit(); }
```

**All three provers:** Same frameworks. Deterministic functions preserve independence.

---

### 9.4 axiom_uniform_elligator / axiom_uniform_elligator_independent

$$
r \sim \text{Uniform}(\mathbb{F}_p) \;\implies\; \text{Elligator}(r) \sim \text{Uniform}(\text{Im}(\text{Elligator}))
$$

The Elligator map on a uniform field element produces a point uniform over the Elligator image (roughly half the curve). Independence is preserved.

**Verus:**
```rust
pub proof fn axiom_uniform_elligator(fe: &FieldElement, point: &RistrettoPoint)
    requires /* point = Elligator(fe) */, is_uniform_field_element(fe),
    ensures is_uniform_over_elligator_image(point),
{ admit(); }
```

**Isabelle/HOL** (best framework) -- CryptHOL's `spmf` monad + `cyclic_group` locale provide the most suitable infrastructure for reasoning about Elligator's measure-preserving properties.

**Lean 4 / Rocq** -- probability frameworks exist but are less developed for this specific use case.

---

### 9.5 axiom_uniform_elligator_sum

$$
P_1 \sim \text{Uniform}(\text{Im}(\text{Elligator})),\;\; P_2 \sim \text{Uniform}(\text{Im}(\text{Elligator})),\;\; P_1 \perp P_2
$$
$$
\implies\; P_1 +_E P_2 \sim \text{Uniform}(G)
$$

The sum of two independent Elligator outputs is uniform over the full Ristretto group. This is why `from_uniform_bytes` uses two Elligator calls plus addition.

**Verus:**
```rust
pub proof fn axiom_uniform_elligator_sum(
    p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires /* sum = p1 + p2, both uniform over Elligator image, independent */
    ensures is_uniform_ristretto_point(sum),
{ admit(); }
```

**Isabelle/HOL** (best framework) -- CryptHOL:
```isabelle
definition elligator_sum_game :: "'a spmf" where
  "elligator_sum_game = do {
    r1 ← uniform UNIV;  r2 ← uniform UNIV;
    let p1 = elligator r1;  let p2 = elligator r2;
    return_spmf (p1 ⊕ p2)
  }"
(* Goal: show elligator_sum_game ≈ uniform (carrier G) *)
```

**Lean 4 / Rocq** -- probability frameworks, no specialised theorem.

---

### 9.6 axiom_uniform_point_add

$$
P_1, P_2 \sim \text{Uniform}(G),\;\; P_1 \perp P_2 \;\implies\; P_1 + P_2 \sim \text{Uniform}(G)
$$

In any finite group, the sum of two independent uniform elements is uniform.

**Verus:**
```rust
pub proof fn axiom_uniform_point_add(
    p1: &RistrettoPoint, p2: &RistrettoPoint, sum: &RistrettoPoint)
    requires /* sum = p1 + p2, both uniform, independent */
    ensures is_uniform_ristretto_point(sum),
{ admit(); }
```

**Isabelle/HOL** (framework) -- CryptHOL `cyclic_group` locale + `uniform`:
```isabelle
locale cyclic_group = group +
  fixes g :: 'a
  assumes generates: "⟨{g}⟩ = carrier G"
```

**Lean 4** (framework) -- `PMF.uniformOfFintype` + group homomorphism properties.

**Rocq** (framework) -- MathComp-Analysis probability over `finGroupType`.

---

### 9.7 axiom_uniform_mod_reduction

$$
X \sim \text{Uniform}([0, 2^{512})) \;\implies\; X \bmod L \;\approx\; \text{Uniform}(\mathbb{Z}_L)
$$

with statistical distance at most L/2⁵¹² ≈ 2⁻²⁵⁹.

**Verus:**
```rust
pub proof fn axiom_uniform_mod_reduction(input: &[u8; 64], result: &Scalar)
    requires scalar_as_nat(result) == bytes_seq_as_nat(input@) % group_order(),
    ensures is_uniform_bytes(input) ==> is_uniform_scalar(result),
{ admit(); }
```

**All three provers:** Standard leftover-hash / modular-reduction bias argument. CryptHOL (Isabelle) has the `advantage` / statistical distance definitions to formalise the 2⁻²⁵⁹ bound.

---

## 10. Axioms with No Existing Correspondent in Any Prover

The following axioms have **no machine-checked counterpart** in Lean 4, Rocq, or Isabelle/HOL. They would all require novel formalisations.

### 10.1 Ristretto Construction

These axioms encode the Ristretto/Decaf quotient-group construction.

#### axiom_ristretto_cross_mul_iff_equivalent

$$
P_1 \sim P_2 \;\Leftrightarrow\; X_1 Y_2 = Y_1 X_2 \;\lor\; X_1 X_2 = Y_1 Y_2
$$

Two well-formed Edwards points are Ristretto-equivalent (differ by a 4-torsion element) iff their projective coordinates satisfy the cross-multiplication check. The four 4-torsion elements {O, (0,−1), (i,0), (−i,0)} yield exactly the two disjoint conditions in the disjunction.

**Reference:** Hamburg (2015) -- "Decaf: Eliminating cofactors through point compression" &sect;4; Ristretto specification &sect;3.2
**URL:** https://eprint.iacr.org/2015/673.pdf ; https://ristretto.group/formulas/equality.html
**Runtime validation:** `test_ristretto_cross_mul_iff_equivalent`

```rust
pub proof fn axiom_ristretto_cross_mul_iff_equivalent(p1: EdwardsPoint, p2: EdwardsPoint)
    requires is_well_formed_edwards_point(p1), is_well_formed_edwards_point(p2),
    ensures ristretto_equivalent(p1, p2) == (X1*Y2 == Y1*X2 || X1*X2 == Y1*Y2),
{ admit(); }
```

#### axiom_ristretto_decode_on_curve

When the Ristretto decode succeeds for field element s, the decoded coordinates (x, y) satisfy the Edwards curve equation. Follows from algebraic substitution of the decode formulas into the curve equation.

**Reference:** Hamburg (2015) -- "Decaf" &sect;3; https://ristretto.group/formulas/decoding.html
**Runtime validation:** `test_ristretto_decode_on_curve` (100 points)

```rust
pub proof fn axiom_ristretto_decode_on_curve(s: nat)
    requires s < p(), ristretto_decode_ok(s),
    ensures is_on_edwards_curve(ristretto_decode_x(s), ristretto_decode_y(s)),
{ admit(); }
```

#### axiom_ristretto_decode_in_even_subgroup

When the Ristretto decode succeeds, the resulting point lies in the even subgroup 2E = {2Q : Q in E}. This is the core property of the Ristretto construction: decoded points lie in the prime-order subgroup. The proof relies on the Jacobi quartic isogeny theory from the Decaf/Ristretto papers.

**Reference:** Hamburg (2015) -- "Decaf" &sect;3; Hamburg (2019) -- "Ristretto"; https://ristretto.group/details/isogenies.html
**URL:** https://eprint.iacr.org/2015/673 ; https://eprint.iacr.org/2020/1400
**Runtime validation:** `test_ristretto_decode_in_even_subgroup` (100+ points)

```rust
pub proof fn axiom_ristretto_decode_in_even_subgroup(s: nat, point: EdwardsPoint)
    requires s < p(), ristretto_decode_ok(s),
        edwards_point_as_nat(point) == (ristretto_decode_x(s), ristretto_decode_y(s), 1, x*y),
    ensures is_in_even_subgroup(point),
{ admit(); }
```

---

### 10.2 Elligator Map

These axioms encode properties of the Elligator2-to-Ristretto map.

#### axiom_elligator_encode_outputs_valid_u

Elligator2 always outputs a valid Montgomery u-coordinate (on the curve, not the twist). Both branches of the map (square and non-square case) yield points satisfying u^3 + Au^2 + u being a quadratic residue.

**Reference:** Bernstein, Hamburg, Krasnova, Lange (2013) -- "Elligator"; RFC 9380 &sect;6.7.1
**URL:** https://www.rfc-editor.org/rfc/rfc9380.html#section-6.7.1

```rust
pub proof fn axiom_elligator_encode_outputs_valid_u(r: nat)
    ensures is_valid_u_coordinate(spec_elligator_encode(r)),
{ admit(); }
```

#### axiom_elligator_on_curve

The Elligator Ristretto map always produces a point satisfying the Edwards curve equation. The map parametrizes points via the Jacobi quartic, and the resulting coordinates always satisfy the curve equation.

**Reference:** Hamburg (2015) -- "Decaf" &sect;4; Ristretto specification &sect;4.3.4
**URL:** https://eprint.iacr.org/2015/673 ; https://ristretto.group/formulas/elligator.html
**Runtime validation:** `test_elligator_on_curve` (250+ inputs)

```rust
pub proof fn axiom_elligator_on_curve(r_0: nat)
    ensures is_on_edwards_curve(
        spec_elligator_ristretto_flavor(r_0).0,
        spec_elligator_ristretto_flavor(r_0).1),
{ admit(); }
```

#### axiom_elligator_nonzero_intermediates

The Elligator map's intermediate N_t = c(r-1)(d-1)^2 - D is always nonzero, and 1 + s^2 != 0 (the Elligator construction never produces s = +/-i even though -1 is a square in GF(p)).

**Reference:** Hamburg (2015) -- "Decaf" &sect;4; Ristretto specification &sect;4.3.4
**URL:** https://eprint.iacr.org/2015/673 ; https://ristretto.group/formulas/elligator.html
**Runtime validation:** `test_elligator_nonzero_denominators` (200+ inputs)

```rust
pub proof fn axiom_elligator_nonzero_intermediates(r_0: nat, s_nat: nat, n_t_nat: nat, d_val_nat: nat)
    requires s_nat < p(), (s_nat, n_t_nat, d_val_nat) == elligator_intermediates(r_0),
    ensures n_t_nat % p() != 0, field_add(1, field_square(s_nat)) != 0,
{ admit(); }
```

#### axiom_elligator_in_even_subgroup

The Elligator Ristretto map always produces a point in the even subgroup 2E, i.e., it is the double of some curve point. The construction naturally produces doubles via the Jacobi quartic parametrization. Combined with the E[4] coset quotient, this gives the prime-order Ristretto group.

**Reference:** Hamburg (2015) -- "Decaf" &sect;3; Hamburg (2019) -- "Ristretto"
**URL:** https://eprint.iacr.org/2015/673 ; https://eprint.iacr.org/2020/1400 ; https://ristretto.group/details/isogenies.html
**Runtime validation:** `test_elligator_in_even_subgroup` (200+ inputs)

```rust
pub proof fn axiom_elligator_in_even_subgroup(r_0: nat)
    ensures forall|point: EdwardsPoint|
        edwards_point_as_affine(point) == spec_elligator_ristretto_flavor(r_0)
            && is_well_formed_edwards_point(point) ==> is_in_even_subgroup(point),
{ admit(); }
```

---

### 10.3 Precomputed Tables

These are computational verification axioms for hardcoded lookup tables. They are justified by construction (the tables are generated from the basepoint) and by interoperability with the Ed25519/Ristretto ecosystem.

#### axiom_ed25519_basepoint_table_valid

The ED25519_BASEPOINT_TABLE contains correct multiples [(2j+1)(16^2)^i B] with bounded limbs. The table is generated by `EdwardsBasepointTable::create(&ED25519_BASEPOINT_POINT)`.

**Reference:** RFC 8032 &sect;5.1 (cites RFC 7748 for edwards25519)
**URL:** https://www.rfc-editor.org/rfc/rfc8032#section-5.1

```rust
pub proof fn axiom_ed25519_basepoint_table_valid()
    ensures is_valid_edwards_basepoint_table(*ED25519_BASEPOINT_TABLE, spec_ed25519_basepoint()),
{ admit(); }
```

#### axiom_affine_odd_multiples_of_basepoint_valid

The AFFINE_ODD_MULTIPLES_OF_BASEPOINT table contains [1B, 3B, 5B, ..., 127B] with bounded limbs for NAF-based scalar multiplication.

**Reference:** RFC 8032 &sect;5.1; Ed25519 reference implementation
**URL:** https://www.rfc-editor.org/rfc/rfc8032#section-5.1

```rust
pub proof fn axiom_affine_odd_multiples_of_basepoint_valid()
    ensures
        naf_lookup_table8_affine_limbs_bounded(AFFINE_ODD_MULTIPLES_OF_BASEPOINT.0),
        is_valid_naf_lookup_table8_affine_coords(
            AFFINE_ODD_MULTIPLES_OF_BASEPOINT.0, spec_ed25519_basepoint()),
{ admit(); }
```

#### axiom_ristretto_basepoint_table_valid

The Ristretto basepoint table is valid. Follows from `axiom_ed25519_basepoint_table_valid` since the Ristretto table is a pointer cast of the Ed25519 table.

**Reference:** Hamburg (2019) -- "Ristretto"; https://eprint.iacr.org/2020/1400
**URL:** https://eprint.iacr.org/2020/1400

```rust
pub proof fn axiom_ristretto_basepoint_table_valid()
    ensures is_valid_edwards_basepoint_table(
        constants::RISTRETTO_BASEPOINT_TABLE.0, spec_ristretto_basepoint()),
{ axiom_ed25519_basepoint_table_valid(); assume(...); }
```

---

All 10 axioms above require defining the Edwards group law and Ristretto/Elligator constructions from scratch in the target prover before they can be stated, let alone proved. Any prover could handle the table verification via its computational kernel (`native_decide`, `native_compute`, `eval`) once the group law is established.

---

## Summary

| Domain | # Axioms | Lean 4 | Rocq | Isabelle/HOL | Best coverage |
|--------|----------|--------|------|--------------|---------------|
| Primality | 2 | framework | framework | framework | All equal |
| Edwards group law | 4 | framework (Weierstrass) | framework | **direct** (AFP) | **Isabelle** |
| Montgomery curve | 3 | framework | **direct** (Fiat-Crypto) | framework | **Rocq** |
| Quadratic residuosity | 5 | framework | framework | framework | All equal |
| Birational equivalence | 3 | framework | framework | framework | All equal |
| Subgroup closure | 1 | framework | framework | framework | All equal |
| Inverse square root | 2 | framework | framework | framework | All equal |
| Hash properties | 2 | none | framework (VST) | framework (AFP) | **Rocq** |
| Probability | 8 | framework | framework | framework (CryptHOL) | **Isabelle** |
| Ristretto/Elligator | 7 | none | none | none | -- |
| Precomputed tables | 3 | none | none | none | -- |
| **Total** | **40** | | | | |

- **30 axioms** have at least framework-level support in one or more provers
- **10 axioms** (Ristretto, Elligator, tables) have no existing counterpart anywhere and require novel formalisation
- **Isabelle** has the strongest single result: a direct, machine-checked proof of Edwards associativity and completeness
- **Rocq** has the strongest applied result: Fiat-Crypto's production-verified Montgomery ladder
- **CryptHOL** (Isabelle) is the most mature framework for the 8 probability axioms
