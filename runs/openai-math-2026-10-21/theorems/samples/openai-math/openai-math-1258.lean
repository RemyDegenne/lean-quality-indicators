namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_1 u_2

open Complex Metric Set Filter Real

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Set Filter Metric

open scoped Topology

open Set Filter Metric Complex

open scoped Topology

open Set Filter Metric Complex

open scoped Topology

open Set Metric Filter Topology

lemma bounded_holomorphic_local_lipschitz {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hb : ∀ z ∈ U, ‖f z‖ ≤ 1)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : closedBall x (2*r) ⊆ U)
    {y z : ℂ} (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖f z-f y‖ ≤ (1/r)*‖z-y‖ := by
  apply (convex_ball x r).norm_image_sub_le_of_norm_deriv_le ?_ ?_ hy hz
  · intro w hw
    apply hf.differentiableAt (hU.mem_nhds (hx ?_))
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hw).le (by linarith))
  · intro w hw
    exact bounded_holomorphic_local_deriv hU hf hb hr hx hw

end CompleteCrouzeix
end
end OAI
