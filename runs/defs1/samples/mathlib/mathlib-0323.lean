@[expose] public section

universe w'' w w' v₁ v₂ v₁' v₂' u₁ u₂ u₁' u₂'

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift D M]

namespace Localization

section

variable (X Y : C)

variable (M)

/-- Given objects `X` and `Y` in a category `C`, this is the property that
all the types of morphisms from `X⟦a⟧` to `Y⟦b⟧` are `w`-small
in the localized category with respect to a class of morphisms `W`. -/
abbrev HasSmallLocalizedShiftedHom : Prop :=
  ∀ (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

end
end Localization
end CategoryTheory
end
