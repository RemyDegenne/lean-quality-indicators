@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]

variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

/-- The canonical pointwise map from a group-valued functor to its coset
functor. -/
def cosetMk : G ⋙ CategoryTheory.forget GrpCat.{w} ⟶ coset i where
  app X := ↾Quotient.mk''
  naturality X Y f := by
    ext x
    rfl

end CategoryTheory.NatTrans
end
end
