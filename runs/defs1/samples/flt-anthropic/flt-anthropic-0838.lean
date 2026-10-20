namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit

set_option autoImplicit false

set_option maxHeartbeats 3200000

p2m_open

open scoped TensorProduct

universe u

noncomputable section

namespace GoodReductionJacobian

p2m_open

namespace RelativeGroupLaw

p2m_open

variable {R : Type u} [CommRing R]

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

section TensorArgument

open Algebra.TensorProduct

variable (G : RelativeGroupLaw R f)

variable (B₁ : CommRingCat.{u}) [Algebra R B₁]

variable (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]

variable (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))

variable (hιe : Set.range G.kwUnitSection.base ⊆ Set.range ι.base)

include hιf

def kwUniversalMul : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁)) ⟶ A :=
  (G.mul (kwTensorStruct (R := R) B₁)
    (kwTensorPoint B₁ ι hιf includeLeft) (kwTensorPoint B₁ ι hιf includeRight)).1

end TensorArgument
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
