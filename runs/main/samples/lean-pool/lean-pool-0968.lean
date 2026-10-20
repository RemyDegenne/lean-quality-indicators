@[expose] public section

open Filter Topology Metric NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma optimalityEqn_contDiff
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφ : ContDiff ℝ 2 φ) (m : E) :
    ContDiff ℝ 1 (optimalityEqn φ m) := by
  unfold optimalityEqn
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  -- The residual r - v - φ(v) is C¹ as a function of (r, v)
  have hres : ContDiff ℝ 1 fun p : E × V =>
      p.1 - (V.subtypeL p.2 : E) - (V.orthogonal.subtypeL (φ p.2) : E) :=
    (contDiff_fst.sub (V.subtypeL.contDiff.comp contDiff_snd)).sub
      (V.orthogonal.subtypeL.contDiff.comp (hφ1.comp contDiff_snd))
  -- fderiv ℝ φ is C¹ (since φ is C²)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  -- The adjoint of (fderiv ℝ φ v) is C¹ in v
  have hDφ_adj : ContDiff ℝ 1 fun v : V =>
      (ContinuousLinearMap.adjoint (fderiv ℝ φ v) : V.orthogonal →L[ℝ] V) :=
    contDiff_adjoint.comp hDφ
  -- Sum: projV(res) + (Dφ(v))†(projW(res))
  exact ((V.orthogonalProjectionOnto : E →L[ℝ] V).contDiff.comp hres).add
    ((hDφ_adj.comp contDiff_snd).clm_apply
      ((V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal).contDiff.comp hres))

end PLAcceleratedNesterovLean
end
end
