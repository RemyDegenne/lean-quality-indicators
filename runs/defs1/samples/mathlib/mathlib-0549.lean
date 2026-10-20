@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open Category DerivedCategory Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

/-- The connecting homomorphism
`(singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧` in the derived
category of `C` when `S` is a short exact short complex in `C`. -/
noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))

end ShortExact
end ShortComplex
end CategoryTheory
end
