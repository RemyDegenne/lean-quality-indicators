namespace OAI

noncomputable section

open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem contDiff_covarianceCLM_joint {V : P → C(Period, E)}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p => covarianceCLM (V p)) := by
  have hc := hV.sub ((contDiff_average_joint hV).comp contDiff_fst)
  rw [contDiff_clm_apply_iff]
  intro m
  simp_rw [covarianceCLM_apply]
  have hi := SmoothParameterIntegral.contDiff_integral
    ((hc.inner ℝ (contDiff_const (c := m))).smul hc) 0 1
  convert hi using 1
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar
    (fun t => inner ℝ (V p t - average (V p)) m • (V p t - average (V p)))).symm

end ClosedSurfaceR4.CovarianceCorrector
end
end OAI
