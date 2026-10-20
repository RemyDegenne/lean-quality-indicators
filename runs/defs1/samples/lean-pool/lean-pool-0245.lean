@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow10ChamberOne

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

/-- Expanded core coefficients after the height adjustment at vertex 5, applied to `allocB`. -/
def bCoeff (d : DegSpec 8 12) (v : Fin 8) : ℤ :=
  if v = 0 then
    positiveChip (d.length 10) + tailContribution (d.length 10) 0 (d.length 10)
  else if v = 1 then
    zeroChip (markC d) - zeroChip (d.length 4)
      + (if 0 < markC d then (0 : ℤ)
          else tailContribution (d.length 4) 0 (d.length 10))
  else if v = 2 then
    positiveChip (d.length 3) + tailContribution (d.length 3) 0 (htB d)
  else if v = 3 then
    zeroChip (d.length 10)
      + (headContribution (d.length 10) 0 (d.length 10)
          + headContribution (d.length 9) (htB d) (d.length 10))
  else if v = 4 then
    zeroChip (d.length 10) + headContribution (d.length 10) 0 (d.length 10)
  else if v = 5 then
    zeroChip (d.length 3)
      + (headContribution (d.length 3) 0 (htB d)
          + tailContribution (d.length 9) (htB d) (d.length 10)
          + tailContribution (d.length 11) (htB d) (d.length 10))
  else if v = 6 then 0
  else 1 + headContribution (d.length 11) (htB d) (d.length 10)

end AtanasovRanganathan.GenusFiveRow10ChamberOne
end
