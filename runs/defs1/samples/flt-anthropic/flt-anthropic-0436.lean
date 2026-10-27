namespace P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible

open scoped TensorProduct Polynomial

universe u v

noncomputable section

namespace DimOneFibreAux

open Polynomial TensorProduct

variable (Λ : Type u) [CommRing Λ] (p : Λ)

variable (A : Type u) [CommRing A] [Algebra Λ A] [Algebra Λ[X] A] [IsScalarTower Λ Λ[X] A]

@[reducible] noncomputable def algPolyFib : Algebra (F₀ Λ p)[X] (Fib Λ p A) :=
  (Polynomial.aeval (R := F₀ Λ p) (xFib Λ p A)).toRingHom.toAlgebra

end DimOneFibreAux
end
end P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible
