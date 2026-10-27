@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverCells4

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow06CoverBase

/-- Closed-cover cell 462 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 24, 4, 29, 6]`; `cell462_check` verifies
its explicit-potential certificate. -/
def cell462 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 24, 4, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

end AtanasovRanganathan.GenusFiveRow06CoverCells4
end
