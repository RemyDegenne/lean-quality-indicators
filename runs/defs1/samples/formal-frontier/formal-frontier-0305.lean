set_option warningAsError true

@[expose] public section

namespace CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

namespace NatTrans

/-- The map of quotient-type colimits induced by a natural transformation. -/
def mapColimitType {X Y : C ⥤ Type w} (α : X ⟶ Y) : X.ColimitType → Y.ColimitType :=
  X.descColimitType (Y.coconeTypes.precompose (fun c => α.app c) (by
    intro c d f
    funext x
    simpa only [Function.comp_apply] using (α.naturality_apply f x)))

end NatTrans
end CategoryTheory
end
