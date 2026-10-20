@[expose] public section

universe w' w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

namespace AttachCells

open MorphismProperty

variable {g f} (c : AttachCells.{w} g f)

include c

lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : ∀ i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

end AttachCells
end HomotopicalAlgebra
end
