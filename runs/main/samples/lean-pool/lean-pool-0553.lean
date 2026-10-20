@[expose] public section

open Finset Polynomial

namespace Zeta32.Arith.Local

export Zeta5Irrational (piPl piPl_monic natDegree_piPl polyPart resP lagrange_basis_eq
  partial_fractionsP natDegree_polyPart_le)

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma zmod_eq_iff_dvd {a b : ℤ} : (a : ZMod p) = b ↔ (p : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.symm

end Zeta32.Arith.Local
end
