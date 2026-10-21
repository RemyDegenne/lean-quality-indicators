namespace OAI

noncomputable section

open Set

open scoped ContDiff Topology

namespace SmoothLocal.HighEquation

open SmoothLocal.Geometry

theorem qMarginObservable_segment_error {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : S ⊆ U)
    {M c L epsilon : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hbound : ∀ w ∈ qCompactTube g S M c, ‖fderiv ℝ (qMarginObservable g) w‖ ≤ L)
    {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1, stateSegment w0 w1 sigma ∈ qCompactTube g S M c)
    (hdist : ‖w1 - w0‖ ≤ epsilon) {sigma : ℝ} (hs : sigma ∈ Icc (0 : ℝ) 1)
    (i : Fin 3) :
    |qMarginObservable g (stateSegment w0 w1 sigma) i - qMarginObservable g w0 i| ≤ L * epsilon := by
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => qMarginObservable g (stateSegment w0 w1 r))
        (fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t) (w1 - w0)) t := by
    have hw := qCompactTube_subset_domain hSU M hc (hsegment t ht)
    have hobs := ((qMarginObservable_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
    exact hobs.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
  have hderivbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t) (w1 - w0)‖ ≤ L * ‖w1 - w0‖ :=
    (fderiv ℝ (qMarginObservable g) (stateSegment w0 w1 t)).le_of_opNorm_le
      (hbound _ (hsegment t (Ico_subset_Icc_self ht))) _
  have hv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hderivbound sigma hs
  simp only [stateSegment_zero, sub_zero] at hv
  have hnorm : ‖qMarginObservable g (stateSegment w0 w1 sigma) - qMarginObservable g w0‖ ≤
      L * epsilon := by
    calc
      _ ≤ (L * ‖w1 - w0‖) * sigma := hv
      _ ≤ L * ‖w1 - w0‖ :=
        mul_le_of_le_one_right (mul_nonneg hL (norm_nonneg _)) hs.2
      _ ≤ L * epsilon := mul_le_mul_of_nonneg_left hdist hL
  have hi := (norm_le_pi_norm
    (qMarginObservable g (stateSegment w0 w1 sigma) - qMarginObservable g w0) i).trans hnorm
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi

end SmoothLocal.HighEquation
end
end OAI
