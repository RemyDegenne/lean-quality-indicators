@[expose] public section

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

namespace CompactExhaustion

variable (K : CompactExhaustion X)

open scoped Classical in
/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : X) : ℕ :=
  Nat.find (K.exists_mem x)

end CompactExhaustion
end
