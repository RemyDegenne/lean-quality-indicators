@[expose] public section

namespace Utilities.Certificate

open MarkedGraphs.Certificate

open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

open Utilities.Certificate.ContractionForestCensusGeneral

namespace DegenerateCoreVertexCut

open Utilities.Certificate.DegenerateSpec CoreVertexCut

variable {n p : ℕ} (d : DegSpec n p) (cut : CoreVertexCut.Data d.core)

/-- Vanishing slots lying wholly in the named side. -/
def leftZero : Finset (Fin p) := d.zeroSlotSet ∩ cut.leftSlots

end DegenerateCoreVertexCut
end Utilities.Certificate
end
