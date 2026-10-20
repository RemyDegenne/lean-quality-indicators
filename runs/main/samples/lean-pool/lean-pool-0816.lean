@[expose] public section

noncomputable section

namespace NavierStokes.NaturalProfile

open Set Filter NaturalAxisBridge NaturalAxisCoefficients

open scoped Topology ContDiff

theorem pullback_second_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    iteratedDeriv 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 =
      Λ ^ 2 * iteratedDeriv 2 (fun Y : ℝ => F (Y, p.2)) (Λ * p.1) := by
  have hs := sliceY_smooth hF hp
  have hs' : ContDiffAt ℝ 1 (deriv (fun Y : ℝ => F (Y, p.2))) (Λ * p.1) := by
    exact (hs.fderiv_right (m := 1)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).clm_apply
        contDiffAt_const
  have hd := ((hs'.differentiableAt (by norm_num)).hasDerivAt.comp p.1
    ((hasDerivAt_id p.1).const_mul Λ)).const_mul Λ
  have heq : deriv (fun X : ℝ => pullback Λ F (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X : ℝ => Λ * deriv (fun Y : ℝ => F (Y, p.2)) (Λ * X)) := by
    have hc : Continuous (fun X : ℝ => (Λ * X, p.2)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)] with X hX
    exact (pullback_hasDerivAt_Y hF Λ (p := (X, p.2)) hX).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  convert! hd.deriv using 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring

end NavierStokes.NaturalProfile
end
end
