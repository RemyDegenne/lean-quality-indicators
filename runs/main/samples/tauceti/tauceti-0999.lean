public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure G}

section DivInvMonoid

variable [DivInvMonoid G] [MeasurableMul G]

theorem measurePreserving_conj (μ : Measure G) [SMulInvariantMeasure (ConjAct G) G μ] (h : G) :
    MeasurePreserving (fun g ↦ h * g * h⁻¹) μ μ :=
  measurePreserving_smul (ConjAct.toConjAct h) μ

end DivInvMonoid
end TauCeti
end
