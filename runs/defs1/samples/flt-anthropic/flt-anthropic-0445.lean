namespace P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

open Polynomial

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

namespace WeierstrassCurve

p2m_open

variable {R : Type*} [CommRing R]

def wrLHS (W : WeierstrassCurve R) (n : ℤ) : R[X] :=
  W.Ψ₂Sq * (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)) ^ 2

end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand
