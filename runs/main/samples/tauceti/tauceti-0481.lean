public section

noncomputable section

open Filter MeasureTheory Set Topology

open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {p : ℝ} {γ : ℝ → X}

section Measurable

variable {α : Type*} [MeasurableSpace α] {F : α → ℝ → X}

theorem measurable_curveAction (hF : ∀ x, Continuous (F x))
    (hm : ∀ s u, Measurable fun x ↦ edist (F x s) (F x u)) (p a b : ℝ) :
    Measurable fun x ↦ curveAction p (F x) a b := by
  have h : Measurable fun q : α × ℝ ↦ metricDerivative (F q.1) q.2 ^ p :=
    (measurable_metricDerivative hF hm).pow_const p
  simp only [curveAction_def]
  exact h.lintegral_prod_right' (ν := volume.restrict (Ι a b))

end Measurable
end PseudoEMetricSpace
end TauCeti
end
end
