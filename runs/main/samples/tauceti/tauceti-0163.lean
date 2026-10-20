public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C] [Preadditive C] [MonoidalPreadditive C]

section Binary

variable {X Y : C} [HasBinaryBiproduct X Y]

theorem rightTrace_biprod (f : X ⊞ Y ⟶ X ⊞ Y) :
    rightTrace f = rightTrace (biprod.inl ≫ f ≫ biprod.fst) +
      rightTrace (biprod.inr ≫ f ≫ biprod.snd) := by
  calc
    rightTrace f = rightTrace ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ f) := by
      simp
    _ = _ := by
      rw [Preadditive.add_comp, rightTrace_add]
      simp only [Category.assoc, rightTrace_comm (biprod.fst : X ⊞ Y ⟶ X),
        rightTrace_comm (biprod.snd : X ⊞ Y ⟶ Y)]

end Binary
end TauCeti
end
