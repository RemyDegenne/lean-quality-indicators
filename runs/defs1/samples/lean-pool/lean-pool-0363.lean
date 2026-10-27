@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverBase

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Endpoint-slope witness 26 for the row-06 closed cover: `alpha` is -2 at slots 8; -1 at slots
9, and zero elsewhere. `beta` is -1 at slots 10, 11; 1 at slots 9; 2 at slots 8, and zero
elsewhere. The nonzero affine potentials occur at vertices 4, 5. -/
def witness26 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, -2], [], []] : List (List ℤ)).getD vertex.val []) }

end AtanasovRanganathan.GenusFiveRow06CoverBase
end
