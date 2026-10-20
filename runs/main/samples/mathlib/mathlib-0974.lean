@[expose] public section

namespace CategoryTheory

universe w v u

open Category Iso

namespace Bicategory

@[inherit_doc] scoped infixr:81 " ◁ " => Bicategory.whiskerLeft

@[inherit_doc] scoped infixl:81 " ▷ " => Bicategory.whiskerRight

@[inherit_doc] scoped notation "α_" => Bicategory.associator

@[inherit_doc] scoped notation "λ_" => Bicategory.leftUnitor

@[inherit_doc] scoped notation "ρ_" => Bicategory.rightUnitor

attribute [instance_reducible, instance] homCategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

@[reassoc (attr := simp)]
theorem whiskerLeft_hom_inv_whiskerRight (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (k : c ⟶ d) :
    f ◁ η.hom ▷ k ≫ f ◁ η.inv ▷ k = 𝟙 (f ≫ g ≫ k) := by
  simp [← whiskerLeft_comp]

end Bicategory
end CategoryTheory
end
