@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow06CoverBase

open GenusFiveRow06Symmetry (Chamber chamber_covers)

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells
      ((((((base ++ [aff [0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, -1,
      0, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++
      [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0])]) ++ [aff [0, 0, 0, 0, 0,
      0, 0, 0, 0, 2, -1, 0, 0]]) = true := by
  decide +kernel

end AtanasovRanganathan.GenusFiveRow06FixedCover
end
