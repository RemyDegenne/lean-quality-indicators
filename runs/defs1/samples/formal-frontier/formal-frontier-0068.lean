@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

/-- The opposite-order generator `b ⊗ m` in the accepted extension. -/
noncomputable def leftPure (M : Presheaves A) (U : Cᵒᵖ)
    (b : B.obj U) (m : M.obj U) : tensorSection A B theta M U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  exact TensorProduct.tmul (A.obj U) b m

end RingedSpaces.Modules
end
