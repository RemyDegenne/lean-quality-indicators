@[expose] public section

open Function MulOpposite

variable {F α β : Type*}

namespace Set

scoped[Pointwise] attribute [instance] Set.one Set.zero

section Inv

scoped[Pointwise] attribute [instance] Set.inv Set.neg

open scoped Pointwise

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]

end InvolutiveInv
end Inv
end Set
end
