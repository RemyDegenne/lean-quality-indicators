@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04CoverCells0

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow04CoverBase

theorem cell37_check :
    cell37.certificate.checkClosed 4 = true := by
  decide +kernel

end AtanasovRanganathan.GenusFiveRow04CoverCells0
end
