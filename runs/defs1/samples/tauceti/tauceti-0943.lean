public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal unitInterval RealInnerProductSpace

namespace TauCeti

section Definition

variable {X : Type*} [MeasurableSpace X] {V W : X → ℝ} {μ : Measure X}

/-- The *potential energy* `∫ V dμ` of a measure `μ` in a potential `V : X → ℝ`, as an extended
real. It is `⊤` when the positive part of `V` has infinite integral against `μ`; otherwise it is the
integral of the positive part minus the integral of the negative part, which is `⊥` when only the
latter is infinite. -/
def potentialEnergy (V : X → ℝ) (μ : Measure X) : EReal :=
  if ∫⁻ x, ENNReal.ofReal (V x) ∂μ = ∞ then ⊤
  else (∫⁻ x, ENNReal.ofReal (V x) ∂μ : EReal) - (∫⁻ x, ENNReal.ofReal (-V x) ∂μ : EReal)

end Definition
end TauCeti
end
end
