@[expose] public section

universe a w p

open CategoryTheory Opposite

open scoped Simplicial TensorProduct

namespace SSet

variable {S T U : SSet.{w}}

/-- The degree map on integral tensor chains: tensor the integral map with the
coefficient identity, then lift to the common universe. -/
noncomputable def tensorNormalizedChainComplexXMap (A : Type a) [AddCommGroup A]
    (f : S ⟶ T) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ⟶
      tensorNormalizedChainComplexX.{a, w, p} A T n :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap ∘ₗ
    (normalizedIntegralMap f n).rTensor A ∘ₗ
      (ULift.moduleEquiv (R := ℤ)).toLinearMap)

end SSet
end
