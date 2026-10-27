@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- Tensor chains in one degree as finitely supported lifted coefficients. -/
noncomputable def tensorNormalizedChainComplexXIsoFinsupp (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ≅
      ModuleCat.of ℤ (S.nonDegenerate n →₀ ULift.{max w p} A) := by
  classical
  exact ((ULift.moduleEquiv (R := ℤ)).trans
    ((TensorProduct.finsuppScalarLeft ℤ A (S.nonDegenerate n)).trans
      (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := ℤ) (M := A)).symm))).toModuleIso

end SSet
end
