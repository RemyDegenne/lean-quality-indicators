@[expose] public section

open Metric Set Topology unitInterval

open scoped Graph

namespace Schoenflies

variable {α β : ℝ}

variable {C : Set Plane}

namespace InitialData

variable {C : Set Plane} (d : InitialData C)

/-- **The target realization of `initialStructure`** — `Γ'` of `prop:initial-pair`. -/
noncomputable def targetRealization : initialStructure.Realization := d.tgt.realization

end InitialData
end Schoenflies
end
