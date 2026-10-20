@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section ModObj

open MonObj AddMonObj

open scoped MonoidalLeftAction

variable (M : C) [MonObj M]

/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ₗ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
@[to_additive]
class ModObj (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ⊵ₗ X ≫ smul = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with multiplication. -/
  mul_smul (X) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul := by cat_disch

end ModObj
end CategoryTheory
end
