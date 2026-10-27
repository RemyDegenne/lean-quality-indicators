@[expose] public section

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₁' v₁'' v₂ v₃ v₄

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

namespace MultilinearMap

section Semiring

variable [Semiring R] [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
  [AddCommMonoid M₂] [Module R M₂]

section Module

variable [Semiring S] [Module S M₂] [SMulCommClass R S M₂]

variable [AddCommMonoid M₃] [Module S M₃] [Module R M₃] [SMulCommClass R S M₃]

variable (S) in
/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `LinearMap.compMultilinearMap` as an `S`-linear equivalence,
and the multilinear version of `LinearEquiv.congrRight`. -/
@[simps! apply symm_apply]
def _root_.LinearEquiv.multilinearMapCongrRight
    [LinearMap.CompatibleSMul M₂ M₃ S R] [LinearMap.CompatibleSMul M₃ M₂ S R] (g : M₂ ≃ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R M₁ M₃ where
  __ := g.toLinearMap.compMultilinearMapₗ S
  invFun := g.symm.toLinearMap.compMultilinearMapₗ S
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

end Module
end Semiring
end MultilinearMap
end
