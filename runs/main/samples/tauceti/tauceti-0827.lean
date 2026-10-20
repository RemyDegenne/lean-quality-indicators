public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane

open scoped MatrixGroups Real Topology

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

attribute [local instance] Complex.finrank_real_complex_fact

theorem mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane {A B C : ℍ} (hAB : A ≠ B)
    (h : C ∈ leftHalfPlane (geodesicBetween A B)) :
    A ∈ leftHalfPlane (geodesicBetween B C) := by
  have hBC : B ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_right A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane h)
  have hC : ((geodesicBetween A B)⁻¹ • C : ℍ).re < 0 := (mem_leftHalfPlane_iff _ _).1 h
  have hre : (geodesicLine 1 (dist A B)).re ≠ ((geodesicBetween A B)⁻¹ • C : ℍ).re := by
    rw [geodesicLine_one_apply, UpperHalfPlane.mk_re]
    exact hC.ne'
  rw [← Set.smul_mem_smul_set_iff (a := (geodesicBetween A B)⁻¹), smul_leftHalfPlane,
    ← geodesicBetween_smul _ hBC, inv_geodesicBetween_smul_left, inv_geodesicBetween_smul_right,
    mem_leftHalfPlane_geodesicBetween_iff_of_re_ne hre, geodesicLine_one_apply,
    UpperHalfPlane.mk_re, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  have hd : 1 < Real.exp (dist A B) ^ 2 :=
    one_lt_pow₀ (Real.one_lt_exp_iff.2 (dist_pos.2 hAB)) two_ne_zero
  refine mul_neg_of_pos_of_neg (by linarith) ?_
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

end TauCeti.UpperHalfPlane
end
end
