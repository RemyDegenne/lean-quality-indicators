@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The residual.**  The core packing gap at every pair of parameters. -/
def CoreGapResidual : Prop := ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → CoreGapAt ε δ

end Nibble.AX1
end
