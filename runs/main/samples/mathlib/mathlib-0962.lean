public section

noncomputable section

open Function Filter Inv MeasureTheory.Measure Module Set TopologicalSpace

open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F]

theorem Integrable.comp_mul_right' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x * R) :=
  (integrable_comp_mul_right_iff g hR).2 hg

end MeasureTheory
end
end
