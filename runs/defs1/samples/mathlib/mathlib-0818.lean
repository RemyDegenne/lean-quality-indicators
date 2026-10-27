@[expose] public section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')

open TensorProduct

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (r : R) (A : Type*) [CommSemiring A] [Algebra R A]

namespace IsLocalization.Away

variable (S) in
/-- The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`. -/
noncomputable abbrev tensorEquiv [IsLocalization.Away r A] :
    S ⊗[R] A ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

end IsLocalization.Away
end
end
