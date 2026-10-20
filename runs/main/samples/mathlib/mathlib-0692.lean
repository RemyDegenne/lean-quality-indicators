@[expose] public section

universe u

open CategoryTheory Limits Opposite TypeCat

open scoped Simplicial

namespace SSet

variable {X Y Z : SSet.{u}}

@[simp]
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  induction x
  simp

end SSet
end
