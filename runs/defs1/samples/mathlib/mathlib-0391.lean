public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- Category where objects have compatible copy and discard operations. -/
class CopyDiscardCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    extends SymmetricCategory C where
  /-- Every object has commutative comonoid structure. -/
  [comonObj : (X : C) → ComonObj X]
  /-- Every object's comonoid structure is commutative. -/
  [isCommComonObj : (X : C) → IsCommComonObj X]
  /-- Tensor products of copies equal copies of tensor products. -/
  copy_tensor (X Y : C) : Δ[X ⊗ Y] = (Δ[X] ⊗ₘ Δ[Y]) ≫ tensorμ X X Y Y := by cat_disch
  /-- Discard distributes over tensor. -/
  discard_tensor (X Y : C) : ε[X ⊗ Y] = (ε[X] ⊗ₘ ε[Y]) ≫ (λ_ (𝟙_ C)).hom := by cat_disch
    /-- Copy on the unit object. -/
  copy_unit : Δ[𝟙_ C] = (λ_ (𝟙_ C)).inv := by cat_disch
    /-- Discard on the unit object. -/
  discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C) := by cat_disch

end CategoryTheory
end
