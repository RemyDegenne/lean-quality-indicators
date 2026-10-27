namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one

set_option autoImplicit false

universe u

open scoped TensorProduct

open KaehlerDifferential

namespace CutAlg

section localization

variable {k : Type u} [Field k] {A P : Type u} [CommRing A] [CommRing P]
    [Algebra k A] [Algebra k P] [Algebra A P] [IsScalarTower k A P]
    [Algebra P k] [Algebra A k] [IsScalarTower A P k]

noncomputable def cotangentEquivOfFormallyEtale [Algebra.FormallyEtale A P] :
    k ⊗[A] Ω[A⁄k] ≃ₗ[k] k ⊗[P] Ω[P⁄k] :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P k k Ω[A⁄k]).symm ≪≫ₗ
    LinearEquiv.baseChange P k _ _ (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A P)

end localization
end CutAlg
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_affine_formallyUnramified_stalkMap_action_one
