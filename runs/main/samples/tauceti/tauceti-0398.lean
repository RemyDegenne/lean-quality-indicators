public section

noncomputable section

namespace Set

open Metric Filter TauCeti Topology

open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isLipschitzChart_refl_setOf_lt_fst {γ : E → ℝ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    IsLipschitzChart {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}
      (AffineIsometryEquiv.refl ℝ _) γ K h r where
  height_pos := hh
  radius_pos := hr
  lipschitzWith := hγ
  image_inter_normalCylinder := by simp

end Set
end
end
