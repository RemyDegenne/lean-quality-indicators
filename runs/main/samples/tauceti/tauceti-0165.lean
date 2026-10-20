public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

variable (a b : R)

variable (W : WeierstrassCurve R)

variable {W} {x y : R}

variable (hψ₂ : IsUnit (W.ψ₂.evalEval x y)) (hΨ₃ : IsUnit (W.Ψ₃.eval x))

namespace UniversalTate

open MvPolynomial (X)

variable {a b}

universe u

theorem equation_curveULift_zero : curveULift.{u}.toAffine.Equation 0 0 := by
  rw [curveULift_eq_tateNormalForm]
  exact equation_tateNormalForm_zero _ _

end UniversalTate
end WeierstrassCurve
end
