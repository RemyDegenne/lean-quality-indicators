@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow06CoverBase

open GenusFiveRow06Symmetry (Chamber chamber_covers)

/-- Contradiction leaf using Farkas receipt 521 to exclude the accumulated affine constraints in
this row-06 branch. -/
def treePart32 : CompactCellTree :=
  .absurd 521

end AtanasovRanganathan.GenusFiveRow06FixedCover
end
