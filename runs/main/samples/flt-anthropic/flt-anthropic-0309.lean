namespace P2MW.S_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite

set_option maxHeartbeats 800000

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

open scoped TensorProduct

namespace P1Arch

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

open scoped TensorProduct

section Toolkit

variable {W : Type u} [CommRing W]

variable {R : Type u} [CommRing R] [Algebra W R]

theorem projQuot_mk (x y r : R) :
    projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

end Toolkit
end P1Arch
end P2MW.S_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
