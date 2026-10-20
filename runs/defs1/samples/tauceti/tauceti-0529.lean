public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe u v w

section Cochains

variable (R : Type*) (A : Type u) (M : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Pullback of scalar cyclic cochains along the augmentation of the forced unitization. -/
def unitizationAugmentationPullback (n : ℕ) :
    cyclicCochains R R M n →ₗ[R] cyclicCochains R (Unitization R A) M n :=
  cyclicCochainsMap M ((Unitization.fstHom R A).toNonUnitalAlgHom :
    Unitization R A →ₗ[R] R) n

end Cochains
end TauCeti
end
end
