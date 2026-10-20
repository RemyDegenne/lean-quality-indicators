@[expose] public section

universe u

open CategoryTheory

namespace BddLat

attribute [instance] BddLat.isBoundedOrder

@[simp]
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl

end BddLat
end
