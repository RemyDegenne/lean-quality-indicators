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

protected lemma hasCompactSupport (f : C_c(α, β)) : HasCompactSupport f := f.hasCompactSupport'

end Basics
end CompactlySupportedContinuousMap
end
