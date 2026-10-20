@[expose] public section

open scoped BigOperators Topology

namespace ClassicalComplexWPT

@[simp]
theorem lastSlice_zero {n : ℕ} (f : Ambient n → ℂ) : lastSlice f 0 = f 0 := by
  rw [lastSlice, ambient_zero_eq]

end ClassicalComplexWPT
end
