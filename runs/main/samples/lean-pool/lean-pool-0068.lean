public section

open MeasureTheory Set Filter Topology

open CKN

noncomputable section

namespace CIV

theorem continuous_dirichletD {m d : ℕ} {g : Vec m → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (dirichletD m d g) := by
  unfold dirichletD
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  by_cases hi : (i : ℕ) < d
  · simp only [hi, ite_true]
    have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec m => fderiv ℝ g y (basisVec i)) :=
      (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact hg'.continuous.pow 2
  · simp only [hi, ite_false]
    exact continuous_const

end CIV
end
end
