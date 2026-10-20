@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow09

open Utilities

open Certificate

open Certificate.ExplicitPotential

open Certificate.DegenerateSpec

open Certificate.DegenerateSpec.DegSpec

open Certificate.StrongSeparator

open Utilities.Certificate.ContractionForestCensusGeneral

open Configurations

open Guarding

open GenusFiveCoreAtlas

open ConfigurationFive

open ConfigurationMarkedThree

open ConfigurationMarkedRow

open ConfigurationChippedTriangle

/-- The chipped triangle read at the target `4`. -/
def heightT4 (d : DegSpec 8 12) (v : Fin 8) : ℕ :=
  if v = 3 then hcT4 d else if v = 4 then htT4 d
    else if v = 5 then hvT4 d else 0

end AtanasovRanganathan.GenusFiveRow09
end
