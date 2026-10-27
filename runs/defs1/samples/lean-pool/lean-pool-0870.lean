@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow08ChamberOne

open Utilities

open Certificate

open Certificate.ExplicitPotential

open Certificate.DegenerateSpec

open Certificate.DegenerateSpec.DegSpec

open Certificate.StrongSeparator

open Utilities.Certificate.ContractionForestCensusGeneral

open Configurations

open GenusFiveCoreAtlas

open ConfigurationFive

open ConfigurationMarkedThree

open ConfigurationMarkedRow

/-- AR's divisor on chamber 1. -/
def rowDivisor (d : DegSpec 8 12) : CFDiv d.graph :=
  markedDivisorTwo d chipWeight (rowMark d) 3 2

end AtanasovRanganathan.GenusFiveRow08ChamberOne
end
