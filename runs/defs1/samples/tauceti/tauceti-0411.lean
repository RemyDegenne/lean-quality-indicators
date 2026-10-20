public section

noncomputable section

open MeasureTheory

namespace TauCeti

universe u v

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- The equivalence between two-marginal couplings and multi-marginal couplings indexed by
`Fin 2`. -/
def couplingEquivMultiCouplingFinTwo : Coupling (μ 0) (μ 1) ≃ MultiCoupling μ where
  toFun := Coupling.toMultiCouplingFinTwo
  invFun := MultiCoupling.toCouplingFinTwo
  left_inv := Coupling.toCouplingFinTwo_toMultiCouplingFinTwo
  right_inv := MultiCoupling.toMultiCouplingFinTwo_toCouplingFinTwo

end TauCeti
end
end
