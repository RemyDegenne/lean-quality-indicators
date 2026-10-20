@[expose] public section

open Function MulOpposite

variable {F α β : Type*}

namespace Set

scoped[Pointwise] attribute [instance] Set.one Set.zero

scoped[Pointwise] attribute [instance] Set.inv Set.neg

open scoped Pointwise

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left

end Mul
end Set
end
