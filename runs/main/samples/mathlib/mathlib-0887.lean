open Filter

open scoped BigOperators ComplexConjugate ENNReal NNReal

public section

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] {f g h : α → E}

@[simp] lemma lpNorm_const (hp : p ≠ 0) (hμ : μ ≠ 0) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow]

end MeasureTheory
end
