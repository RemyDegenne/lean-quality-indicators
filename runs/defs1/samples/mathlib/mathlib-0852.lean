@[expose] public section

open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma. -/
def energy : ℚ :=
  ((∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : ℚ) / (#P.parts : ℚ) ^ 2

end Finpartition
end
