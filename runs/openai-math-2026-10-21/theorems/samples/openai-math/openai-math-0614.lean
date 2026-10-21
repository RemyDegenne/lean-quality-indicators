namespace OAI

noncomputable section

namespace YauCounterexamples

open Set Filter Function Metric

open scoped Topology

open Set Filter Function Metric

open scoped Topology ContDiff InnerProductSpace

open Filter Set

open scoped Topology

open Set Filter Function Metric

open scoped Topology ContDiff InnerProductSpace

open Set Filter Function Metric Topology Manifold

open scoped Topology ContDiff

open Set Filter Function Metric Topology Manifold MeasureTheory

open scoped Topology ContDiff

lemma profilePeriodize_eventually_zero {f : ProfilePlane → ℝ} {r R : ℝ}
    (hrR : r < R) (hf : ∀ z, r < ‖z‖ → f z = 0) (x : ProfilePlane)
    (hx : ∀ k, R ≤ ‖x-profileLatticePoint k‖) :
    profilePeriodize f =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrR)] with z hz
  have hd : ‖z-x‖ < R-r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hz0 : ∀ k, f (z-profileLatticePoint k) = 0 := by
    intro k
    apply hf
    have ht : ‖x-profileLatticePoint k‖ ≤ ‖z-x‖+‖z-profileLatticePoint k‖ := by
      calc
        _ = ‖(x-z)+(z-profileLatticePoint k)‖ := by congr 1; abel
        _ ≤ ‖x-z‖+‖z-profileLatticePoint k‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev x z]
    linarith only [ht,hd,hx k]
  simp [profilePeriodize,hz0]

end YauCounterexamples
end
end OAI
