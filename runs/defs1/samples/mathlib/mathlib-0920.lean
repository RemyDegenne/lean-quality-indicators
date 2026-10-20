@[expose] public section

universe u v w

open Filter Set

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

/-- Copy of a `CocompactMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

end Basics
end CocompactMap
end
