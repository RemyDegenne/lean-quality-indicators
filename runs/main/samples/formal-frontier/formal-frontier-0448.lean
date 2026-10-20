@[expose] public section

noncomputable section

universe u v

namespace Finsupp

variable (K : Type u) [Field K] {ι : Type v} (s : Set ι)

theorem single_mem_supportedSubcoalgebra {i : ι} (a : K) (hi : i ∈ s) :
    single i a ∈ supportedSubcoalgebra K s := by
  rw [Subcoalgebra.mem_iff, supportedSubcoalgebra_toSubmodule]
  exact single_mem_supported K a hi

end Finsupp
end
end
