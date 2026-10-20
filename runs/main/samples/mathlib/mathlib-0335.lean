@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated

open Edge CompStruct

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

section homotopy_category

variable [Quasicategory₂ X]

namespace HomotopyCategory₂

lemma homMk_eq_iff_homotopicL {f g : Edge x₀ x₁} :
    homMk f = homMk g ↔ HomotopicL f g :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound h⟩

end HomotopyCategory₂
end homotopy_category
end SSet.Truncated
end
