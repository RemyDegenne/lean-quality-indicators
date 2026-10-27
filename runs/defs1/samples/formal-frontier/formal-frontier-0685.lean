@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]

variable {H G : Functor C GrpCat.{w}} (i : H ⟶ G)

namespace IsPointwiseNormal

variable [h : IsPointwiseNormal i]

/-- The canonical pointwise quotient map. -/
def quotientMk : G ⟶ quotient i where
  app X := GrpCat.ofHom (QuotientGroup.mk' (i.app X).hom.range)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

end IsPointwiseNormal
end CategoryTheory.NatTrans
end
end
