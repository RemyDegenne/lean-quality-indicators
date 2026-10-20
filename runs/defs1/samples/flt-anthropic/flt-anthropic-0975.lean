namespace P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace P2MMultE

open scoped TensorProduct

section DualSide

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]

variable {L : Type*} [Field L] [Algebra F L]

variable {S : Submonoid (WithConv (A →ₐ[F] L))}

noncomputable def dualBC : L ⊗[F] Module.Dual F (QS S) →ₗ[L] Module.Dual L (L ⊗[F] QS S) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.ringLmapEquivSelf L L (Module.Dual F (QS S) →ₗ[F] Module.Dual L (L ⊗[F] QS S))).symm
      (Module.Dual.baseChange L))

end DualSide
end P2MMultE
end P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
