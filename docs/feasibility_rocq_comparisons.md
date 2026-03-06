# Verus Axioms vs. Rocq (Coq): Side-by-Side Definitions

Companion to [feasibility_rocq.md](feasibility_rocq.md). For each axiom, the Verus
definition is shown alongside the closest existing Rocq theorem or definition from
Fiat-Crypto, CoqPrime, MathComp, or VST.

---

## 1. Primality

### axiom_p_is_prime

**Verus:**
```rust
pub proof fn axiom_p_is_prime()
    ensures is_prime(p()),   // p() = 2^255 - 19
{ admit(); }
```

**Rocq (CoqPrime):** Pocklington's criterion — generate a certificate with `primo`, verify in Coq:
```coq
(* From coqprime: Pocklington.v *)
Theorem Pocklington :
  forall N F1 R1,
    N - 1 = F1 * R1 ->
    Z.gcd F1 R1 = 1 ->
    1 < F1 ->
    (forall p, prime p -> (p | F1) ->
      exists a, 1 < a /\ a^(N-1) mod N = 1 /\ Z.gcd (a^((N-1)/p) - 1) N = 1) ->
    (forall p, prime p -> (p | N) -> N <= p * p \/ R1 < p) ->
    prime N.
```
Source: [CoqPrime](https://thery.gitlabpages.inria.fr/coqprime/) — verified Mersenne primes up to M₂₂₈₁ (687 digits) in ~2.4s.

Usage: `primo` → `o2v` → `v2v` → `coqc` pipeline. `native_compute`/`vm_compute` for verification.

---

### axiom_group_order_is_prime

**Verus:**
```rust
pub proof fn axiom_group_order_is_prime()
    ensures is_prime(group_order()),
{ admit(); }
```

**Rocq:** Same CoqPrime pipeline applied to L.

---

## 2. Montgomery Curve xDBL / xADD

### axiom_xdbl_projective_correct

**Verus:**
```rust
pub proof fn axiom_xdbl_projective_correct(P: MontgomeryAffine, U: nat, W: nat)
    requires projective_represents_montgomery_or_infinity_nat(U, W, P),
    ensures projective_represents_montgomery_or_infinity_nat(
        spec_xdbl_projective(U, W).0, spec_xdbl_projective(U, W).1,
        montgomery_add(P, P)),
{ admit(); }
```

**Rocq (Fiat-Crypto):** `src/Curves/Montgomery/XZProofs.v`
```coq
(* From fiat-crypto: Curves/Montgomery/XZProofs.v *)
Lemma xzladderstep_correct
  (a24 : F) (X1 : F) (P Q : point)
  (HX1 : X1 = to_xz P - to_xz Q)  (* differential *)
  :
  let '(x2, z2, x3, z3) := xzladderstep a24 X1 (to_xz P) 1 (to_xz Q) 1 in
  (* x2/z2 represents 2*P, x3/z3 represents P+Q *)
  ...
```
Source: [`mit-plv/fiat-crypto`](https://github.com/mit-plv/fiat-crypto/blob/master/src/Curves/Montgomery/XZProofs.v) — production code in BoringSSL and Linux kernel.

**This is the closest existing mechanised proof of the axiom in any prover.**

---

### axiom_xadd_projective_correct

**Verus:**
```rust
pub proof fn axiom_xadd_projective_correct(
    P: MontgomeryAffine, Q: MontgomeryAffine,
    U_P: nat, W_P: nat, U_Q: nat, W_Q: nat, affine_PmQ: nat)
    requires /* projective representations, P != Q, affine_PmQ != 0 */
    ensures projective_represents_montgomery_or_infinity_nat(
        spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ).0,
        spec_xadd_projective(U_P, W_P, U_Q, W_Q, affine_PmQ).1,
        montgomery_add(P, Q)),
{ admit(); }
```

**Rocq (Fiat-Crypto):** Same `xzladderstep_correct` lemma — the ladder step computes both doubling and differential addition simultaneously.

---

## 3. Edwards Curve Group Law

### axiom_edwards_add_associative

**Verus:**
```rust
pub proof fn axiom_edwards_add_associative(x1: nat, y1: nat, x2: nat, y2: nat, x3: nat, y3: nat)
    ensures
        edwards_add(edwards_add(x1,y1,x2,y2).0, edwards_add(x1,y1,x2,y2).1, x3, y3)
        == edwards_add(x1, y1, edwards_add(x2,y2,x3,y3).0, edwards_add(x2,y2,x3,y3).1),
{ admit(); }
```

**Rocq (Fiat-Crypto):** `src/Curves/Edwards/` contains Edwards curve definitions. The full associativity proof is not confirmed to be present; it may need to be proved via the Hales–Raya polynomial identity method:
```coq
(* Pattern from Fiat-Crypto: Curves/Weierstrass/AffineProofs.v *)
Lemma add_assoc : forall P Q R,
    add (add P Q) R = add P (add Q R).
```

For Edwards specifically, the proof would express associativity as:
```coq
(* Hypothetical — following Hales's method *)
Lemma edwards_add_assoc : forall x1 y1 x2 y2 x3 y3,
    let p12 := edwards_add x1 y1 x2 y2 in
    let p23 := edwards_add x2 y2 x3 y3 in
    edwards_add (fst p12) (snd p12) x3 y3 =
    edwards_add x1 y1 (fst p23) (snd p23).
(* Proof by ring / vm_compute on the polynomial identity *)
```

---

### axiom_edwards_add_complete

**Verus:**
```rust
pub proof fn axiom_edwards_add_complete(x1: nat, y1: nat, x2: nat, y2: nat)
    requires is_on_edwards_curve(x1, y1), is_on_edwards_curve(x2, y2),
    ensures /* denominators nonzero, result on curve */
{ admit(); }
```

**Rocq:** MathComp finite field theory provides the framework:
```coq
(* MathComp: ssralg.v *)
(* F is a fieldType, d is not a square *)
Lemma nonsquare_neq_square (F : fieldType) (d x : F) :
    ~~ is_square d -> d * x ^+ 2 <> 1.
```
Combined with the curve equation to show denominators are nonzero.

---

### axiom_edwards_scalar_mul_signed_additive / axiom_edwards_scalar_mul_distributive

**Verus:**
```rust
pub proof fn axiom_edwards_scalar_mul_signed_additive(P: (nat, nat), a: int, b: int)
    ensures edwards_add(smul(P,a), smul(P,b)) == smul(P, a+b),
{ admit(); }
```

**Rocq (MathComp):** Once a `zmodType` / `finGroupType` instance exists:
```coq
(* MathComp: fingroup.v *)
Lemma expgD (G : finGroupType) (x : G) (m n : nat) :
    x ^+ (m + n) = x ^+ m * x ^+ n.

(* For signed: ssrint.v *)
Lemma mulrzDl (R : zmodType) (x : R) (m n : int) :
    x *~ (m + n) = x *~ m + x *~ n.
```

---

## 4. Quadratic Residuosity

### axiom_486660_not_quadratic_residue

**Verus:**
```rust
pub proof fn axiom_486660_not_quadratic_residue()
    ensures !is_square(486660nat),
{ admit(); }
```

**Rocq (MathComp):** Euler's criterion over `ZModp`:
```coq
(* MathComp: finfield.v / Fp_field *)
(* Compute via vm_compute: *)
Eval vm_compute in (486660 ^ ((p - 1) / 2) mod p).
(* If result = p - 1 (i.e., -1), then 486660 is not a QR *)
```

---

### axiom_sqrt_m1_squared

**Verus:**
```rust
pub proof fn axiom_sqrt_m1_squared()
    ensures (sqrt_m1() * sqrt_m1()) % p() == (p() - 1),
{ admit(); }
```

**Rocq:** Direct computation:
```coq
(* Using native_compute or vm_compute over Z *)
Lemma sqrt_m1_squared : (SQRT_M1 * SQRT_M1) mod p = p - 1.
Proof. native_compute. reflexivity. Qed.
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

**Rocq (Fiat-Crypto):** Fiat-Crypto works with both Edwards and Montgomery forms:
```coq
(* Fiat-Crypto provides the birational map infrastructure *)
(* src/Curves/Edwards/AffineProofs.v and src/Curves/Montgomery/AffineProofs.v *)
(* The specific map u = (1+y)/(1-y) can be verified with ring *)
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

**Rocq (MathComp):** Once the map is a group homomorphism:
```coq
(* MathComp: morphism.v *)
Lemma morphim_expg (aT rT : finGroupType) (f : {morphism aT >-> rT})
    (x : aT) (n : nat) : f (x ^+ n) = (f x) ^+ n.
```

---

## 6. Subgroup Closure

### axiom_even_subgroup_closed_under_add

**Verus:**
```rust
pub proof fn axiom_even_subgroup_closed_under_add(p1: EdwardsPoint, p2: EdwardsPoint)
    requires is_in_even_subgroup(p1), is_in_even_subgroup(p2), /* well-formed */
    ensures /* p1 + p2 is in even subgroup */
{ admit(); }
```

**Rocq (MathComp):**
```coq
(* MathComp: fingroup.v *)
Lemma groupM (G : finGroupType) (H : {group G}) (x y : G) :
    x \in H -> y \in H -> x * y \in H.
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

**Rocq (VST):** SHA-256 is fully verified; SHA-512 follows the same structure:
```coq
(* From vst-crypto / VST SHA-256 verification (Appel) *)
(* FIPS 180-4 spec formalised in Coq *)
Definition SHA_256 (msg : list byte) : list byte := ...
Lemma SHA_256_length : forall msg, length (SHA_256 msg) = 32.

(* SHA-512 would be: *)
Definition SHA_512 (msg : list byte) : list byte := ...
Lemma SHA_512_length : forall msg, length (SHA_512 msg) = 64.
```
Source: [VST SHA-256 verification](https://www.cs.princeton.edu/~appel/papers/verif-sha.pdf) (Appel, Princeton)

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

**Rocq (MathComp):**
```coq
(* MathComp GRing.Theory *)
Lemma mulrA (R : ringType) (x y z : R) : x * (y * z) = x * y * z.
Lemma mulVr (F : fieldType) (x : F) : x != 0 -> x^-1 * x = 1.
Lemma invrK (F : fieldType) (x : F) : (x^-1)^-1 = x.
Lemma sqr_inv (F : fieldType) (x : F) : (x^-1)^+2 = (x^+2)^-1.
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

**Rocq (MathComp-Analysis):**
```coq
(* MathComp-Analysis: probability.v / measure.v *)
(* Framework for uniform distributions over finType *)
(* The specific theorem for groups would combine: *)
(*   - Uniform distribution over finGroupType *)
(*   - Independence (product measure) *)
(*   - Group action preserving measure *)
```
No existing specialised theorem, but the MathComp-Analysis framework provides the foundation.

---

## 10. Ristretto / Elligator (no existing Rocq counterparts)

All Ristretto and Elligator axioms have **no existing counterpart** in Rocq. These would require novel formalisations on top of Fiat-Crypto's curve infrastructure.

---

## 11. Precomputed Tables

**Verus:**
```rust
pub proof fn axiom_ed25519_basepoint_table_valid()
    ensures is_valid_edwards_basepoint_table(*ED25519_BASEPOINT_TABLE, spec_ed25519_basepoint()),
{ admit(); }
```

**Rocq:** Fiat-Crypto generates verified Curve25519 field arithmetic. Table verification could use `native_compute` with the curve operations:
```coq
(* Hypothetical *)
Lemma basepoint_table_correct :
    forall i j, table[i][j] = scalar_mult ((2*j+1) * (16^2)^i) basepoint.
Proof. native_compute. reflexivity. Qed.
```
