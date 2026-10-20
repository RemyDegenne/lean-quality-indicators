public section

open Polynomial

namespace TauCeti

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

theorem norm_eval_hasseDeriv_le_pow_of_norm_sub_le_one {Q : R[X]} {α z : R} {k r : ℕ}
    {δ C₁ : ℝ} (hQ : (Q.natDegree : ℝ) ≤ δ * r) (hQC : Q.l1Norm ≤ C₁ ^ r)
    (hz : ‖z - α‖ ≤ 1) :
    ‖(hasseDeriv k Q).eval z‖ ≤ (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by
  have hα : 1 ≤ 1 + ‖α‖ := le_add_of_nonneg_right (norm_nonneg α)
  have hC₁ : 0 ≤ C₁ ^ r := Q.l1Norm_nonneg.trans hQC
  -- On the ball, `max 1 ‖z‖ ≤ 1 + ‖α‖`.
  have hzα : max 1 ‖z‖ ≤ 1 + ‖α‖ :=
    max_le hα <| (norm_le_norm_add_norm_sub' z α).trans (by rw [add_comm]; gcongr)
  calc
    ‖(hasseDeriv k Q).eval z‖ ≤
        (hasseDeriv k Q).l1Norm * max 1 ‖z‖ ^ (hasseDeriv k Q).natDegree :=
      norm_eval_le_l1Norm_mul _ _
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * (1 + ‖α‖) ^ Q.natDegree :=
      mul_le_mul (l1Norm_hasseDeriv_le_pow hQ hQC)
        ((pow_le_pow_left₀ (by positivity) hzα _).trans
          (pow_le_pow_right₀ hα ((natDegree_hasseDeriv_le Q k).trans tsub_le_self)))
        (by positivity) (by positivity)
    _ ≤ (2 ^ δ) ^ r * C₁ ^ r * ((1 + ‖α‖) ^ (1 + δ)) ^ r := by
      gcongr
      exact (Real.pow_le_rpow_pow_of_le_mul hα hQ).trans <| by
        gcongr
        linarith
    _ = (2 ^ δ * (1 + ‖α‖) ^ (1 + δ) * C₁) ^ r := by ring

end SeminormedRing
end TauCeti
end
