namespace OAI

open Complex

namespace Mahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

lemma contDiffAt_dcLinear_order {u : E → ℂ} {x : E} (q : ℕ)
    (hu : ContDiffAt ℝ (q+1) u x) : ContDiffAt ℝ q (dcLinear u) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

end Mahler
end OAI
