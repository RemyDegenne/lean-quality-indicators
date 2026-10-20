@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace SSet

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

@[reassoc]
theorem homologyZeroPoint_homology₀Iso (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    homologyZeroPoint X R x ≫ (X.homology₀Iso R).hom =
      Sigma.ι (fun _ : X.π₀ ↦ R) (.mk x) := by
  dsimp only [homologyZeroPoint]
  simpa only [Category.assoc] using
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x

end SSet
end
end
