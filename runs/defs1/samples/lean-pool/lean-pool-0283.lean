@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow08ChamberTwo

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

open ConfigurationChippedTriangle

/-- The second chamber marks slot 4 at `markY` and slot 7 at `markX`; other slots receive offset
zero. -/
def rowMark (d : DegSpec 8 12) (e : Fin 12) : ℕ :=
  if e = 4 then markY d else if e = 7 then markX d else 0

end AtanasovRanganathan.GenusFiveRow08ChamberTwo
end
