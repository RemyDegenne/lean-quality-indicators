@[expose] public section

namespace LowGenus.GenusFourRow097Closed

open Utilities

open Utilities.Certificate.DegenerateSpec

open Utilities.Certificate

open Utilities.Certificate.ClosedFaceCensus

open Utilities.Certificate.ClosedCoreSymmetry

open Utilities.Certificate.ClosedContraction

open Utilities.Certificate.ContractionForestCensusGeneral

open AtanasovRanganathan.Configurations

section Ramps

/-- The census hypothesis every closed-orthant march needs: `rep`-equality is
witnessed by a chain of vanishing slots.  Free for `RowProof.censusSpec`, whose
`rep` is `compFold` of the vanishing set (`compFold_iff`). -/
def RepGen (d : DegSpec 6 9) : Prop :=
  ∀ u v : Fin 6, d.rep u = d.rep v →
    ReachIn d.core (Finset.univ.filter fun e : Fin 9 => d.length e = 0) u v

end Ramps
end LowGenus.GenusFourRow097Closed
end
