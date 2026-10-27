@[expose] public section

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}

variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

namespace LiftRightAdjoint

variable {U : A ⥤ B} {F : B ⥤ A} (L : C ⥤ B) (U' : A ⥤ C)

variable (adj₁ : F ⊣ U) (adj₂ : L ⋙ F ⊣ U')

variable [HasCoreflexiveEqualizers C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homset equivalence which helps show that `L` is a left adjoint. -/
@[simps!]
noncomputable def constructRightAdjointEquiv (h : ∀ X : B, RegularMono (adj₁.unit.app X)) (Y : C)
    (X : B) : (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃ (L.obj Y ⟶ X) :=
  calc
    (Y ⟶ constructRightAdjointObj _ _ adj₁ adj₂ X) ≃
        { f : Y ⟶ U'.obj (F.obj X) //
          f ≫ U'.map (F.map (adj₁.unit.app X)) = f ≫ (otherMap _ _ adj₁ adj₂ X) } :=
      Fork.IsLimit.homIso (limit.isLimit _) _
    _ ≃ { g : F.obj (L.obj Y) ⟶ F.obj X // F.map (adj₁.unit.app _≫ U.map g) =
        g ≫ F.map (adj₁.unit.app _) } := by
      apply (adj₂.homEquiv _ _).symm.subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, otherMap,
        ← adj₂.homEquiv_naturality_right_symm, adj₂.homEquiv_unit, ← adj₂.unit_naturality_assoc,
        adj₂.homEquiv_counit]
      simp
    _ ≃ { z : L.obj Y ⟶ U.obj (F.obj X) //
        z ≫ U.map (F.map (adj₁.unit.app X)) = z ≫ adj₁.unit.app (U.obj (F.obj X)) } := by
      apply (adj₁.homEquiv _ _).subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).injective.eq_iff, adj₁.homEquiv_unit,
        adj₁.homEquiv_unit, adj₁.homEquiv_unit, eq_comm]
      simp
    _ ≃ (L.obj Y ⟶ X) := (Fork.IsLimit.homIso (unitEqualizes adj₁ h X) _).symm

end LiftRightAdjoint
end CategoryTheory
end
