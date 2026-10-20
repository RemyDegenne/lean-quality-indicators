@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

theorem cell7_check :
    cell7.certificate.checkClosed 4 = true := by
  decide +kernel

end AtanasovRanganathan.GenusFiveRow03FixedCover
end
