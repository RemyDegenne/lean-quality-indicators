@[expose] public section

variable {F α β γ : Type*} [TopologicalSpace α]

@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000)
  "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

open scoped CompactlySupported

namespace CompactlySupportedContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β]

/-- Copy of a `CompactlySupportedContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : C_c(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

end Basics
end CompactlySupportedContinuousMap
end
