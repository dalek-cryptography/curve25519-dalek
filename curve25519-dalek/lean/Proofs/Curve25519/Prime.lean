module
public import Proofs.Curve25519.Basic
import Proofs.Curve25519.Certificates.Prime
public section

/-! # Primality of `p` and `L`

`p_prime` and `L_prime`, from the Lucas certificates of `Proofs.Curve25519.Certificates.Prime`, the
`Fact` instances that make `ZMod p` and `ZMod L` fields, and the `Fact` instances `2 < p` and
`p % 2 = 1` (`p` is odd) that Mathlib's and `Proofs.Curve25519.Models.Field.Sign`'s lemmas take. -/

namespace curve25519

/-- `p = 2^255 - 19` is prime. -/
theorem p_prime : p.Prime := by
  rw [p_eq_numeral]
  exact Proofs.p_numeral_prime

/-- `L = 2^252 + 27742317777372353535851937790883648493` is prime. -/
theorem L_prime : L.Prime := by
  rw [L_eq_numeral]
  exact Proofs.L_numeral_prime

instance : Fact p.Prime := ⟨p_prime⟩

instance : Fact L.Prime := ⟨L_prime⟩

instance instFactTwoLtP : Fact (2 < p) := ⟨two_lt_p⟩

instance instFactPModTwo : Fact (p % 2 = 1) := ⟨p_mod_two⟩

end curve25519
