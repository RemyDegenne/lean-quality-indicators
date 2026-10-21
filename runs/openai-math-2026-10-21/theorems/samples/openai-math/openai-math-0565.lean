namespace OAI

open Complex Set

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleResolventMoment_succ (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) (n : ℕ) :
    T * circleResolventMoment T r n = circleResolventMoment T r (n + 1) := by
  have hi (j : ℕ) : CircleIntegrable (fun z : ℂ => z ^ j • resolvent T z) 0 r := by
    apply ContinuousOn.circleIntegrable hr
    intro z hz
    have hzr : ‖z‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact ((continuousAt_id.pow j).smul
      (spectrum.hasDerivAt_resolvent_const_left (hres z hzr)).continuousAt).continuousWithinAt
  have hp : CircleIntegrable (fun z : ℂ => z ^ n • (1 : E →L[ℂ] E)) 0 r := by
    exact ((continuous_id.pow n).smul continuous_const).continuousOn.circleIntegrable hr
  have hz : (∮ z in C(0, r), z ^ n • (1 : E →L[ℂ] E)) = 0 := by
    rw [circleIntegral.integral_smul_const,
      (differentiable_id.pow n).diffContOnCl.circleIntegral_eq_zero hr, zero_smul]
  have hmap := circleIntegral_map_clm
    (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) T) (hi n)
  change (∮ z in C(0, r), T * (z ^ n • resolvent T z)) =
    T * (∮ z in C(0, r), z ^ n • resolvent T z) at hmap
  unfold circleResolventMoment
  rw [mul_smul_comm, ← hmap]
  congr 1
  calc
    (∮ z in C(0, r), T * (z ^ n • resolvent T z)) =
        ∮ z in C(0, r), z ^ (n + 1) • resolvent T z - z ^ n • (1 : E →L[ℂ] E) := by
      apply circleIntegral.integral_congr hr
      intro z hz'
      have hzr : ‖z‖ = r := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz'
      dsimp only
      rw [mul_smul_comm, operator_mul_resolvent T (hres z hzr), smul_sub,
        smul_smul, pow_succ]
    _ = ∮ z in C(0, r), z ^ (n + 1) • resolvent T z := by
      rw [circleIntegral.integral_sub (hi (n + 1)) hp, hz, sub_zero]

end
end DefocusingNLS
end OAI
