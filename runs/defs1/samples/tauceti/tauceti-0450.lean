public section

noncomputable section

open MeasureTheory

namespace TauCeti

universe u v

namespace Coupling

variable {X : Fin 2 → Type v} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, ProbabilityMeasure (X i)}

/-- A two-marginal coupling, viewed as a `Fin 2`-indexed multi-marginal coupling. -/
def toMultiCouplingFinTwo (π : Coupling (μ 0) (μ 1)) : MultiCoupling μ :=
  ⟨π.1.map (MeasurableEquiv.piFinTwo X).symm,
    π.2.isMultiCoupling_piFinTwo⟩

end Coupling
end TauCeti
end
end
