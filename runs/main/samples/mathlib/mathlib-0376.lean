@[expose] public section

variable {M : Type*} {N : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}

export OneMemClass (one_mem)

export ZeroMemClass (zero_mem)

namespace Submonoid

@[to_additive]
lemma toSubsemigroup_injective : (toSubsemigroup : Submonoid M → Subsemigroup M).Injective :=
  fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ by congr!

end Submonoid
end NonAssoc
end
