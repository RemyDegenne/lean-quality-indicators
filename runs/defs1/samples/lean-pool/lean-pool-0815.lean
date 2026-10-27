@[expose] public section

noncomputable section

open CategoryTheory Finset

open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]

variable (Z : Center C)

variable {D : Type u} [Category.{v'} D]

variable (F : C ⥤ D)

namespace Fact52

/-- The object part of `C → D`. -/
def CtoDObj : Obj → DObj
  | .X => .X
  | .Y => .Y

end Fact52
end CategoryTheory.Dilatations
end
end
