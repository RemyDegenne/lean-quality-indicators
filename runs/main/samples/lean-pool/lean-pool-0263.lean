@[expose] public section

noncomputable section

namespace EulerGevreyCorrectionSourceBounds

open Set Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevGevreyOperators
  EulerGevreyRadiusReduction EulerGevreyRestriction EulerH6Nonlinear EulerSobolevTransport
  EulerGevreyOrderZero EulerGevreyNonlinearEstimate EulerGevreyUniformConstants
  EulerCorrectionEnergyData EulerSobolevCoefficientPressure EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]

variable {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
  {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
  {P : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}

theorem pressure_smallerRadius_bound (S : SpatialBudget period hq D P R)
    (N : ℕ) (hNP : N ≤ P) (hN : N + 6 ≤ q + 1) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R t) (E DE : ℝ)
    (e : SobolevSpace period ((q + 1) + 1))
    (he : weightedNorm period 6 N r e ≤ E)
    (hde : (∑ i : Fin 4, weightedNorm period 6 N r (derivativeOperator period (q + 1) i e)) ≤ DE) :
    weightedNorm period 6 N r (D.pressure period hq t e) ≤
      2*S.M*sourceBound period S.B0 S.B1 S.A0 S.A2 S.residual E DE := by
  have hM : 0 ≤ S.M := zero_le_one.trans S.M_one_le
  have hsmall : 4*S.M*(r*S.Rc) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrR S.Rc_nonneg) (by positivity)).trans
      (S.radius_small t)
  rw [CorrectionData.pressure, weightedNorm_neg period 6 N hN]
  exact (weightedNorm_pressure period (D.metric.jet t) D.κ D.direction D.coercivity D.coercivity_pos
    (D.metric_pos t) N hN r S.Rc S.M hr S.Rc_nonneg S.M_one_le (S.inverse_six t) hsmall
    (fun l hl hlN => S.metric_derivatives t l hl (hlN.trans hNP)) _).trans
      (mul_le_mul_of_nonneg_left
        (rawSource_smallerRadius_bound period S N hNP hN t r hr hrR E DE e he hde) (by positivity))

end EulerGevreyCorrectionSourceBounds
end
end
