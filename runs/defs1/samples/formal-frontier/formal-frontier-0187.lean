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

def internalInclusion : h.internalGrp ⟶ targetInternalGrp (G := G) :=
  Monoidal.GrpFunctorCategory.inverse.map
    (Functor.whiskerRight h.inclusion GrpTypeEquivalenceGrp.inverse)

end IsPointwiseSubgroup
end CategoryTheory.NatTrans
end
end
