@[expose] public section

namespace Homogenization

open scoped ENNReal

namespace H1Function

/-- Construct an H¹ function from a compactly supported C¹ function and its classical gradient. -/
noncomputable def ofContDiff {d : ℕ} {U : Set (Vec d)} (_hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) : H1Function U :=
  { toFun := f
    grad := fun x i => (fderiv ℝ f x) (basisVec i)
    memL2 := by
      have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
      exact (hf_cont.memLp_of_hasCompactSupport hf_supp).restrict U
    gradMemL2 := by
      intro i
      have hderiv_cont : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using
          (hf.continuous_fderiv (by simp)).clm_apply continuous_const
      have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
        simpa using hf_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact (hderiv_cont.memLp_of_hasCompactSupport hderiv_supp).restrict U
    hasWeakGradient := HasWeakGradientOn.of_contDiff hf }

end H1Function
end Homogenization
end
