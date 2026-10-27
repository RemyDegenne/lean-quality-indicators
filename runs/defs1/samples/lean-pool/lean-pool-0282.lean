@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
  [Nonempty {S : Finset V // S ∈ Pp.parts}]

/-- **The density product of a cluster triple.** -/
noncomputable def dProd (th : Finset {S : Finset V // S ∈ Pp.parts}) : ℝ :=
  dOpp G Pp th 0 * dOpp G Pp th 1 * dOpp G Pp th 2

end Nibble.AX1
end
