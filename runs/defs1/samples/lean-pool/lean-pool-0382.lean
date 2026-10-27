@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow14FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Closed-cover cell 55 for the fixed row-14 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 6, 0, 3, 0, 20, 0]`; `cell55_check` verifies its
explicit-potential certificate. -/
def cell55 : CoordinateCell row14Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 6, 0, 3, 0, 20, 0] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
      aff [0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      aff [0, -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]] }

end AtanasovRanganathan.GenusFiveRow14FixedCover
end
