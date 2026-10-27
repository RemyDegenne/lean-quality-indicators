@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Category

variable {C : Type u} [Category.{v} C]

section

variable {X Y : C}

variable [BinaryCoproductDisjoint X Y]

namespace IsInitial

/-- `X ×[X ⨿ Y] Y` is initial. -/
noncomputable def ofBinaryCoproductDisjoint [HasBinaryCoproduct X Y]
    [HasPullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr] :
    IsInitial (pullback (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  ofBinaryCoproductDisjointOfIsColimitOfIsLimit (colimit.isColimit _) (pullback.isLimit _ _)

end IsInitial
end
end CategoryTheory.Limits
end
