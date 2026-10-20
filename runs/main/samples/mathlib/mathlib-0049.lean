@[expose] public section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w' w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w} [Category.{w'} D]

noncomputable section

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

variable (P : Cᵒᵖ ⥤ D)

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

@[simp]
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plusLift_unique
  rw [← Category.assoc, ← J.toPlus_naturality, Category.assoc, J.toPlus_plusLift]

end
end CategoryTheory.GrothendieckTopology
end
