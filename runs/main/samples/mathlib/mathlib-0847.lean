@[expose] public section

open Function Multiset OrderDual

variable {F α β γ ι : Type*}

namespace Finset

section Sup

variable [SemilatticeSup α] [OrderBot α]

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

@[to_dual (attr := simp)]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)

end Sup
end Finset
end
