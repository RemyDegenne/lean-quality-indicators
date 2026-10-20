@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- The degreewise comparison to normalized chains, obtained by applying inverse
normalized coordinates after the tensor coordinates. Its target is the whole
normalized degree, not the coefficient Finsupp object. -/
noncomputable def tensorNormalizedChainComplexXIso (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (n : ℕ) :
    tensorNormalizedChainComplexX.{a, w, p} A S n ≅
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X n :=
  tensorNormalizedChainComplexXIsoFinsupp.{a, w, p} A S n ≪≫
    (S.normalizedChainComplexXIsoFinsupp (ModuleCat.of ℤ (ULift.{max w p} A)) n).symm

end SSet
end
