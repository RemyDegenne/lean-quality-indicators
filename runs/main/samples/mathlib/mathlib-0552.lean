public section

open Set

variable {R : Type*}

namespace Nat

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsOrderedAddMonoid R] [FloorSemiring R]

@[bound]
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊ :=
  sub_lt_iff_lt_add.2 <| lt_floor_add_one a

end LinearOrderedRing
end Nat
end
