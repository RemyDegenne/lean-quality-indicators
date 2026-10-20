@[expose] public section

open Complex Filter Function Metric Set

open scoped NNReal Topology

namespace CarlsonFunctions.SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

open scoped Classical in
theorem norm_sub_le_of_separately_analytic_bounded {f : (ι → ℂ) → F}
    {c : ι → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ closedBall c (2 * r), ∀ i,
      AnalyticAt ℂ (fun w => f (update z i w)) (z i))
    (hM : ∀ z ∈ closedBall c (2 * r), ‖f z‖ ≤ M)
    {x y : ι → ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖f y - f x‖ ≤ (Fintype.card ι : ℝ) * (M / r) * ‖y - x‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c (mem_closedBall_self (by positivity)))
  have hsmall : closedBall c r ⊆ closedBall c (2 * r) := closedBall_subset_closedBall (by linarith)
  have hdiff (z : ι → ℂ) (i : ι) (w : ℂ) (hw : update z i w ∈ closedBall c (2 * r)) :
      DifferentiableAt ℂ (fun v => f (update z i v)) w := by
    simpa only [update_idem, update_self] using (hf _ hw i).differentiableAt
  have hcoord (z : ι → ℂ) (hz : z ∈ closedBall c r) (i : ι) (w : ℂ)
      (hw : w ∈ closedBall (c i) r) :
      ‖f (update z i w) - f z‖ ≤ (M / r) * ‖w - z i‖ := by
    have hder (v : ℂ) (hv : v ∈ closedBall (c i) r) :
        ‖deriv (fun a => f (update z i a)) v‖ ≤ M / r := by
      have hp := update_mem_closedBall_of_mem hr.le hz i hv
      have hball : closedBall (update z i v) r ⊆ closedBall c (2 * r) :=
        closedBall_subset_closedBall' (by linarith [mem_closedBall.mp hp])
      have hslice := norm_partialDeriv_le_of_slice (f := f) (z := update z i v) i hr
        (fun a ha => (hdiff (update z i v) i a
          (hball (update_mem_closedBall hr.le ha))).differentiableWithinAt)
        (fun a ha => hM _ (hball (update_mem_closedBall hr.le (sphere_subset_closedBall ha))))
      simpa only [partialDerivCarlson, update_idem, update_self] using hslice
    have hzi : z i ∈ closedBall (c i) r := (dist_pi_le_iff hr.le).mp (mem_closedBall.mp hz) i
    simpa only [update_eq_self] using
      (convex_closedBall (c i) r).norm_image_sub_le_of_norm_deriv_le
        (fun v hv => hdiff z i v (hsmall (update_mem_closedBall_of_mem hr.le hz i hv)))
        hder hzi hw
  have hprod : closedBall c r = Set.pi univ (fun i => closedBall (c i) r) := closedBall_pi c hr.le
  have hsum := norm_sub_le_sum_of_update (C := M / r)
    (fun z hz i w hw => hcoord z (hprod.symm ▸ hz) i w hw) (hprod ▸ hx) (hprod ▸ hy)
  refine hsum.trans ?_
  calc
    ∑ i, (M / r) * ‖y i - x i‖ ≤ ∑ i : ι, (M / r) * ‖y - x‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm (y - x) i)
        (div_nonneg hM0 hr.le))
    _ = _ := by simp [mul_assoc]

end CarlsonFunctions.SeveralComplexVariables
end
