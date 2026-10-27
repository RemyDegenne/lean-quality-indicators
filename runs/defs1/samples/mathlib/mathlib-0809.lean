@[expose] public section

universe s t w v u

namespace CategoryTheory.Limits.ColimitPresentation

variable {C : Type u} [Category.{v} C]

variable {J : Type*} {I : J → Type*} [Category* J] [∀ j, Category (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

set_option linter.unusedVariables false in
/-- The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different category structure. -/
@[nolint unusedArguments]
def Total (P : ∀ j, ColimitPresentation (I j) (D.obj j)) : Type _ :=
  Σ j, I j

end CategoryTheory.Limits.ColimitPresentation
end
