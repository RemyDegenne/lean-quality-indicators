namespace P2MW.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod

set_option Elab.async false

section Inl_A3_SL2ZModFacts

namespace Ihara

p2m_open

open Matrix Polynomial

open scoped MatrixGroups

section SmallPrimes

variable {R : Type*} [CommRing R]

theorem pow_twelve_eq_one_SL2_ZMod {p : ℕ} (hp : p = 2 ∨ p = 3) (A : SL(2, ZMod p)) :
    A ^ 12 = 1 := by
  apply Subtype.ext
  rw [sl2coeZ_pow, sl2coeZ_one]
  refine pow_twelve_eq_one_of_sq_eq ?_ (sq_eq_trace_smul_sub_one A)
  generalize Matrix.trace (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = t
  rcases hp with rfl | rfl
  · revert t; decide
  · revert t; decide

end SmallPrimes
end Ihara
end Inl_A3_SL2ZModFacts
end P2MW.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
