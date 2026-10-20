@[expose] public section

universe u v w

noncomputable section

variable (R : Type u) (X : Type v) [CommRing R]

local notation "lib" => FreeNonUnitalNonAssocAlgebra

local notation "lib.lift" => FreeNonUnitalNonAssocAlgebra.lift

local notation "lib.of" => FreeNonUnitalNonAssocAlgebra.of

local notation "lib.lift_of_apply" => FreeNonUnitalNonAssocAlgebra.lift_of_apply

local notation "lib.lift_comp_of" => FreeNonUnitalNonAssocAlgebra.lift_comp_of

namespace FreeLieAlgebra

variable {R X}

theorem Rel.addLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a + b) (a + c) := by
  rw [add_comm _ b, add_comm _ c]; exact h.add_right _

end FreeLieAlgebra
end
end
