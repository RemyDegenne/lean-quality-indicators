@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

export R0Space (specializes_symm)

export R0Space (specializes_symmetric)

theorem Dense.sdiff_finset [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    (t : Finset X) : Dense (s \ t) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert, ← union_singleton, ← sdiff_sdiff]
    exact ih.sdiff_singleton _

end Separation
end
