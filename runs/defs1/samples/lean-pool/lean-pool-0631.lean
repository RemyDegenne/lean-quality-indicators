@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset Utilities.CommonOffsetRounding

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-- The rounded coarse divisor of a family of chips. -/
def coarseChips {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) : CFDiv spec.graph :=
  ∑ i, oneChip (chips i).coarseVertex

end Utilities.Certificate.SubdivisionGraph.Spec
end
