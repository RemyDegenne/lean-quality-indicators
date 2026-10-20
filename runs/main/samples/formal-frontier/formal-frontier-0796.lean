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

lemma mem_range_iff (X : C) (y : G.obj X) :
    y ∈ Set.range (p.app X) ↔ y ∈ h.subgroup X :=
  Set.ext_iff.mp (h.range_eq X) y

end IsPointwiseSubgroup
end CategoryTheory.NatTrans
end
end
