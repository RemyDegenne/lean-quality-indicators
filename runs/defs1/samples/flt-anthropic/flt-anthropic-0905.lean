namespace P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

p2m_open

namespace InvariantDerivation

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

scoped instance instIsDomainA : IsDomain (A W) := inferInstance

noncomputable scoped instance instFieldL : Field (L W) := inferInstance

noncomputable scoped instance instCommRingL : CommRing (L W) := inferInstance

noncomputable scoped instance instAlgKA : Algebra K (A W) := inferInstance

noncomputable scoped instance instAlgKL : Algebra K (L W) := inferInstance

noncomputable scoped instance instAlgAL : Algebra (A W) (L W) := inferInstance

noncomputable scoped instance instModL : Module (L W) (L W) := inferInstance

noncomputable scoped instance instModLop : Module (L W)ᵐᵒᵖ (L W) := inferInstance

scoped instance instCentral : IsCentralScalar (L W) (L W) := inferInstance

noncomputable scoped instance instCommRingT : CommRing (T W) := inferInstance

noncomputable scoped instance instRingT : Ring (T W) := inferInstance

noncomputable scoped instance instSemiringT : Semiring (T W) := inferInstance

noncomputable scoped instance instMonoidT : Monoid (T W) := inferInstance

noncomputable scoped instance instMulT : Mul (T W) := inferInstance

noncomputable scoped instance instAddT : Add (T W) := inferInstance

noncomputable scoped instance instAddCommMonoidT : AddCommMonoid (T W) := inferInstance

noncomputable def fY : L W :=
  2 * y₀ W + algebraMap K (L W) W.a₁ * x₀ W + algebraMap K (L W) W.a₃

end InvariantDerivation
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
