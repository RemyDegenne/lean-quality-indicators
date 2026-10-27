@[expose] public section

universe a b c w p

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

variable {A : Type a} {B : Type b} {C : Type c}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The identity on integral simplex classes tensored with an additive coefficient
homomorphism, with balanced source and target padding. -/
noncomputable def tensorNormalizedCoefficientMap (g : A →+ B) (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, max b p} A S n ⟶
      tensorNormalizedChainComplexX.{b, w, max a p} B S n :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    g.toIntLinearMap.lTensor (S.nonDegenerate n →₀ ℤ) ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

end SSet
end
