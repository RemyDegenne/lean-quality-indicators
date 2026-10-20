public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

section Minuscule

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable (b : (IsKilling.rootSystem H).Base) (mu : Dual K H)

variable {b mu}

attribute [local instance] Classical.propDecidable

theorem IsMinuscule.finrank_irreducibleQuotient_eq_card_orbit (h : IsMinuscule b mu) :
    finrank K (irreducibleQuotient b mu) =
      Nat.card (MulAction.orbit (IsKilling.rootSystem H).weylGroup mu) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
  exact finrank_eq_card_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
    (isHighestWeightVector_irreducibleQuotientGenerator b mu)
    (lieSpan_irreducibleQuotientGenerator_eq_top b mu) h.2

end Minuscule
end TauCeti
end
