@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated

open Edge CompStruct

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

section homotopy_category

variable [Quasicategory₂ X]

/--
See `Edge.comp`
-/
@[no_expose]
noncomputable def Edge.compStruct (f : Edge x₀ x₁) (g : Edge x₁ x₂) : CompStruct f g (f.comp g) :=
  (Quasicategory₂.fill21 f g).some.2

end homotopy_category
end SSet.Truncated
end
