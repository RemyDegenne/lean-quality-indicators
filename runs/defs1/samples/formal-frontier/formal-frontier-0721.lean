public section

universe a b w p

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

/-- The morphism taking a lifted coefficient to degree-zero homology of terminal
normalized tensor chains, using inverse degree-zero coordinates followed by
Mathlib's cycles isomorphism and homology projection. -/
noncomputable def tensorNormalizedCoefficientToHomologyZero
    (A : Type a) [AddCommGroup A] (T : SSet.{w}) (hT : IsTerminal T) :
    ModuleCat.of ℤ (ULift.{max w p} A) ⟶
      (tensorNormalizedChainComplex.{a, w, p} A T).homology 0 := by
  exact (tensorNormalizedZeroIsoCoefficient.{a, w, p} A T hT).inv ≫
    (ChainComplex.cycles₀Iso (tensorNormalizedChainComplex.{a, w, p} A T)).inv ≫
      (tensorNormalizedChainComplex.{a, w, p} A T).homologyπ 0

end SSet
end
