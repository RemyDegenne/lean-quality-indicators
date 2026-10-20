namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing

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

omit hιf in

def kwTensorStruct : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁))
    ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R ((B₁ : Type u) ⊗[R] B₁)))

end TensorArgument
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
