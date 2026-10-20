@[expose] public section

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

open WalkingPair

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y

end CategoryTheory.Limits
end
