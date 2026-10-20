namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

namespace GenKerSol

p2m_open

variable {K : Type} [Field K] [DecidableEq K]

section OnCurve

variable (W : WeierstrassCurve K)

theorem evalEval_ψ_sq (n : ℤ) {x y : K} (hxy : W.toAffine.Equation x y) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h1 : (Affine.CoordinateRing.mk W) ((W.ψ n) ^ 2) = (Affine.CoordinateRing.mk W) (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨r, hr⟩ := (AdjoinRoot.mk_eq_mk).mp h1
  have h2 := congrArg (Polynomial.evalEval x y) hr
  rw [evalEval_sub, evalEval_pow, evalEval_C, evalEval_mul] at h2
  have h3 : Polynomial.evalEval x y (WeierstrassCurve.Affine.polynomial W) = 0 := hxy
  rw [h3, zero_mul, sub_eq_zero] at h2
  exact h2

end OnCurve
end GenKerSol
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_addOrderOf_eq_forall_isRoot_level_fst_of_raw_rigidDataH1Pow
