public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {Ω : Set ℂ} {g : ℂ → ℂ}

theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv
    {f : ℂ → ℂ} {q b : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ 0)
    (hgf : EqOn g (fun w => (f (-w⁻¹) - q) / b)
      (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := fun z hz => by
    rw [Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  apply (tendsto_mul_logDeriv_deriv_comp_neg_inv_upperHalfPlaneSet Metric.isOpen_ball
    hball (Metric.mem_ball_self hr) hcont hholo hreal hupper hinj).congr'
  rw [eventuallyEq_inf_principal_iff]
  have hinv : Tendsto (fun z : ℂ => -z⁻¹) (cobounded ℂ) (nhds 0) := by
    simpa only [neg_zero] using (tendsto_inv₀_cobounded (α := ℂ)).neg
  filter_upwards [hinv.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)] with z hzball hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hnegInv : -z⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hz
  -- Off the origin, the inverse coordinate of the inverse coordinate is the original map.
  have heq : (fun w : ℂ => g (-w⁻¹)) =ᶠ[𝓝 z] fun w : ℂ => (f w - q) / b := by
    filter_upwards [((continuousAt_inv₀ hz0).neg).preimage_mem_nhds
      ((Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet).mem_nhds
        ⟨hzball, hnegInv⟩)] with w hw
    calc
      g (-w⁻¹) = (f (-(-w⁻¹)⁻¹) - q) / b := hgf hw
      _ = (f w - q) / b := by rw [inv_neg, inv_inv, neg_neg]
  have hderiv : (deriv fun w : ℂ => (f w - q) / b) = fun w => deriv f w / b := by
    ext w
    simp only [deriv_div_const, deriv_sub_const]
  rw [(logDeriv_congr_nhds heq.deriv).eq_of_nhds, hderiv]
  simp only [div_eq_mul_inv, logDeriv_mul_const z b⁻¹ (inv_ne_zero hb)]

end TauCeti
end
