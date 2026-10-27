@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace SSet

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

/-- The degree-zero homology class represented by a vertex of a simplicial set. -/
noncomputable def homologyZeroPoint (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    R ⟶ X.homology R 0 :=
  (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex R).homologyπ 0

end SSet
end
end
