public section

noncomputable section

open Filter MeasureTheory Set Topology

open scoped ENNReal NNReal

namespace TauCeti

namespace RepresentsStieltjes

variable {μ ν : Measure ℝ≥0} {a b c d : ℝ≥0} {f g : ℝ → ℝ}

lemma eq_div_add_add_integral_inv_add (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) :
    f t = (a : ℝ) / t + (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ :=
  h.2.2 t ht

end RepresentsStieltjes
end TauCeti
end
end
