@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

/-- The original-order generator `m ⊗ b` for arbitrary `b`. -/
noncomputable def rightPure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) : rightSectionCat A B theta M U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  letI := rightModule A B theta M U
  exact TensorProduct.tmul (A.obj U) m b

end RingedSpaces.Modules
end
