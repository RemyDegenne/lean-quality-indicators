namespace P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two

set_option autoImplicit false

universe u

open Polynomial

theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2) :
    W.IsTwoKernel (X - C (Q.coordsOrZero).1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_X_sub_C _).le
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C, if_neg one_ne_zero, sub_zero]
  ·
    have hQ0 : Q ≠ 0 := by
      intro h; rw [h, addOrderOf_zero] at hQ; exact absurd hQ (by norm_num)
    have h2 : 2 • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
    rcases Q with _ | ⟨x, y, hxy⟩
    · exact absurd rfl hQ0
    · rw [WeierstrassCurve.Affine.Point.coordsOrZero_some, Polynomial.dvd_iff_isRoot]
      exact WeierstrassCurve.eval_Psi2Sq_of_two_nsmul_eq_zero hxy h2

end P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two
