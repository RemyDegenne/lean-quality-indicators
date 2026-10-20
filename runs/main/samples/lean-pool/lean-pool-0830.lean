@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells
      (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0,
      -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0,
      0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0,
      0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0,
      1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation
      (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0,
      0, 0]]) = true := by
  decide +kernel

end AtanasovRanganathan.GenusFiveRow03FixedCover
end
