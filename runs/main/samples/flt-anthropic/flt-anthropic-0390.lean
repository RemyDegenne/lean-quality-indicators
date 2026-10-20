namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace NodeChord

section coefficients

variable (W : WeierstrassCurve ℤ)

lemma curve_a₁ : (curve W).a₁ = (W.a₁ : AlgebraicClosure ℚ) := by
  show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₁) = _
  rw [eq_intCast, map_intCast]

end coefficients
end NodeChord
end
end P2MW.S_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
