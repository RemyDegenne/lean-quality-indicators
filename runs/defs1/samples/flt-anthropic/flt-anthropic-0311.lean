set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]

def ssNodePairsQExp : Set (Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :=
  {s | s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2}

end TwoComponent
end ModularCurve
end
