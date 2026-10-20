namespace P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace DualExist

p2m_open

section EndRing

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k]
  (W : WeierstrassCurve F) [W.IsElliptic]

abbrev Pt := (W.baseChange k).toAffine.Point

end EndRing
end DualExist
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_dualIsogenyExistence_rationalEndSubring
