@[expose] public section

namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {X Y : C} (f g : X ⟶ Y)

open IsSplitCoequalizer

variable {f g}

section

open Limits

/-- A split coequalizer clearly induces a cofork. -/
@[simps! pt]
def IsSplitCoequalizer.asCofork {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    Cofork f g := Cofork.ofπ h t.condition

end
end CategoryTheory
end
