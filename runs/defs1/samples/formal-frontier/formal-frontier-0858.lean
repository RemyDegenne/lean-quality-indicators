@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonObj

universe v₁ v₂ u₁ u₂ v u w

namespace CategoryTheory.NatTrans

variable {C : Type w} [Category.{v} C]

variable {F : C ⥤ Type u} {G : C ⥤ GrpCat.{u}}
  (p : F ⟶ G ⋙ forget GrpCat.{u})

namespace IsPointwiseSubgroup

variable {p} (h : NatTrans.IsPointwiseSubgroup p)

def targetInternalGrp : Grp (C ⥤ Type u) :=
  Monoidal.GrpFunctorCategory.inverseObj (targetInternalFunctor (G := G))

end IsPointwiseSubgroup
end CategoryTheory.NatTrans
end
end
