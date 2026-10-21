namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology

lemma radialEta_fderiv_scale {s : ℝ} (hs : 0<s) (x : WeylSpace) :
    fderiv ℝ (radialEta radialProfile s) x =
      s⁻¹^4 • fderiv ℝ (radialEta radialProfile 1) (s⁻¹ • x) := by
  have hd := (((radialEta_smooth 1).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s⁻¹)).const_smul (s⁻¹^3)
  rw [radialEta_as_scale hs]
  refine hd.fderiv.trans ?_
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]
  congr 1

end ScalarConductivity
end
end OAI
