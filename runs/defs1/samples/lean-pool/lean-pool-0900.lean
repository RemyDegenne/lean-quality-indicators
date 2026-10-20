@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow04CoverBase

open GenusFiveRow04Symmetry (Chamber chamber_covers)

/-- Contradiction leaf using Farkas receipt 1321 to exclude the accumulated affine constraints
in this row-04 branch. -/
def treePart120 : CompactCellTree :=
  .absurd 1321

end AtanasovRanganathan.GenusFiveRow04FixedCover
end
