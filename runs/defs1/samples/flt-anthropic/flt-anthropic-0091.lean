namespace P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u v w z

namespace NilYoneda

section TestPairs

variable {R : Type u} [CommRing R] {σ : Type}

def transition {N M : ℕ} (h : N ≤ M) : TestRing R σ M →ₐ[R] TestRing R σ N :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

end TestPairs
end NilYoneda
end
end P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent
