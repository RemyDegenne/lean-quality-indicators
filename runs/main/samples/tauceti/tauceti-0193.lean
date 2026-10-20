public section

open scoped TensorProduct

namespace TauCeti

variable (R S A L : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [LieRing L] [LieAlgebra R L]

@[simp]
theorem cancelBaseChange_tmul (a : A) (s : S) (x : L) :
    cancelBaseChange R S A L (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = (s • a) ⊗ₜ[R] x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S A a x s

end TauCeti
end
