@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex
  AlgebraicTopology.DoldKan

open scoped Simplicial

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X Y : SSet.{w}) (f : X ⟶ Y) (R : C)

/-- The split mono `X.normalizedChainComplex R ⟶ X.chainComplex R`. -/
noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

end SSet
end
