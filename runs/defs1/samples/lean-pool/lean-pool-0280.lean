@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04CoverCells0

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow04CoverBase

/-- Closed-cover cell 64 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 8, 0, 0, 5]`; `cell64_check` verifies its
explicit-potential certificate. -/
def cell64 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1],
      aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1],
      aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0,
      1]] }

end AtanasovRanganathan.GenusFiveRow04CoverCells0
end
