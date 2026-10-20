namespace P2MW.S_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

universe u

namespace ModularCurve

p2m_open

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

section Existence

variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime]

omit [IsAlgClosed K] in

theorem eval_preΨ_eq_zero_of_nsmul_eq_zero [DecidableEq K] [W.IsElliptic] (hp2 : p ≠ 2) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hP : p • Point.some x y h = 0) :
    (W.preΨ p).eval x = 0 := by
  rw [WeierstrassCurve.preΨ_ofNat]
  exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ((Fact.out : p.Prime).odd_of_ne_two hp2) h).mp hP

end Existence
end ModularCurve
end P2MW.S_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
