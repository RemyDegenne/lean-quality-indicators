public section

open Finset

namespace TauCeti

namespace UniformHypergraph

variable {r : ℕ} {V : Type*}

section BlockDensity

variable [DecidableEq V]

@[simp]
theorem blockDensity_univ [Fintype V] (H : UniformHypergraph r V) :
    H.blockDensity Finset.univ = H.edgeDensity := by
  rw [blockDensity_def, edgeDensity_def, Finset.card_univ,
    Finset.filter_true_of_mem fun e _ => Finset.subset_univ e]

end BlockDensity
end UniformHypergraph
end TauCeti
end
