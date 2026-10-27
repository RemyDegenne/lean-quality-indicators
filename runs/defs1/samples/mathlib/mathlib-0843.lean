@[expose] public section

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite CategoryTheory Functor

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

namespace FormalCoproduct

set_option backward.defeqAttrib.useBackward true in
/-- A way to create isomorphisms in the category of formal coproducts, by creating an `Equiv`
between the indexing sets, and then correspondingly isomorphisms of each component. -/
@[simps!] def isoOfComponents {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
    (h : ∀ i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := { f := e, φ := fun i ↦ (h i).hom }
  inv := { f := e.symm, φ := fun i ↦ eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

end FormalCoproduct
end Limits
end CategoryTheory
end
