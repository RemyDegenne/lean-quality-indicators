@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow10ChamberTwo

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

open ConfigurationMarkedTripod

open ConfigurationEleven

/-- Expanded core coefficients of the flat-height script applied to the second-chamber
`allocFlat`. -/
def fCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    zeroChip (markA d) - zeroChip (d.length 10)
      + (if 0 < markA d then (0 : ℤ)
          else tailContribution (d.length 10) 0 (d.length 4))
  else if v = 1 then
    positiveChip (d.length 4) + tailContribution (d.length 4) 0 (d.length 4)
  else if v = 2 then
    1 + tailContribution (d.length 3) 0 (d.length 4)
  else if v = 3 then
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  else if v = 4 then
    zeroChip (d.length 4) + headContribution (d.length 4) 0 (d.length 4)
  else if v = 5 then
    headContribution (d.length 3) 0 (d.length 4)
  else if v = 6 then 0
  else 1

end AtanasovRanganathan.GenusFiveRow10ChamberTwo
end
