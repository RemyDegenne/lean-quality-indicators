public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C]

namespace FactorsThrough

variable {P Q : ObjectProperty C} {W X Y Z : C} {f : X ⟶ Y}

theorem comp_left (hf : FactorsThrough P f) (g : W ⟶ X) : FactorsThrough P (g ≫ f) := by
  obtain ⟨A, hA, i, p, rfl⟩ := (factorsThrough_iff P f).1 hf
  rw [← Category.assoc]
  exact factorsThrough_comp P hA (g ≫ i) p

end FactorsThrough
end CategoryTheory.ObjectProperty
end
