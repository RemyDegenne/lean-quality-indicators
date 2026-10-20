namespace P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open

namespace ModularCurve

p2m_open

namespace TransGen

open WeierstrassCurve WeierstrassCurve.Affine

section transport

variable {F : Type*} {L : Type*} [Field F] [Field L] (f : F →+* L) {W₀ : WeierstrassCurve F}

def pmap : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

end transport
end TransGen
end ModularCurve
end P2MW.S_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728
