@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow14FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Closed-cover cell 38 for the fixed row-14 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 14, 0, 3, 0, 4, 0]`; `cell38_check` verifies its
explicit-potential certificate. -/
def cell38 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 14, 0, 3, 0, 4, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

end AtanasovRanganathan.GenusFiveRow14FixedCover
end
