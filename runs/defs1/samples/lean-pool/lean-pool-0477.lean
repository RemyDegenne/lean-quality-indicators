@[expose] public section

open Finset

namespace Utilities.Certificate.WindowProfile

open Utilities.Certificate

open Utilities

open SubdivisionGraph

namespace Data

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

/-- The initial endpoint of a slot's signed slope window. -/
def startPosition (data : Data spec) (edge : Fin p) :
    spec.PathPosition edge :=
  ⟨data.start edge, by
    have hOrder := data.start_le_stop edge
    have hStop := data.stop_le_length edge
    omega⟩

end Data
end Utilities.Certificate.WindowProfile
end
