set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

namespace Bimon

variable (C)

variable {C}

/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
def equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

end Bimon
end CategoryTheory
end
end
