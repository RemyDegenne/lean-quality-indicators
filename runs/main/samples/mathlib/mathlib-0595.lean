@[expose] public section

open MulOpposite

open scoped Pointwise

variable {α β γ : Type*}

namespace Finset

open scoped Pointwise

section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

@[to_additive]
lemma union_smul_inter_subset_union [DecidableEq α] : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_union_inter_subset_union

end SMul
end Finset
end
