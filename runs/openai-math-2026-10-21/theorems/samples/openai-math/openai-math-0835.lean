namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity

section

open scoped ContDiff Topology

open Set Function Filter MeasureTheory

open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by simp) z)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change planarCurl α z =
    fderiv ℝ (fun y => α y (0,1)) z (1,0) - fderiv ℝ (fun y => α y (1,0)) z (0,1)
  rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _),
    fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  rfl

end
end HigherDimensionalBallPacking.Rigidity
end
end OAI
