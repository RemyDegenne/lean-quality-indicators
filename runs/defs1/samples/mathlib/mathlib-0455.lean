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

/-- The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
def equivMonComonUnitIsoApp (M : Bimon C) :
    M ≅ (toMonComon C ⋙ ofMonComon C).obj M :=
  Comon.mkIso' (equivMonComonUnitIsoAppX M)

end Bimon
end CategoryTheory
end
end
