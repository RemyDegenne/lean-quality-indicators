@[expose] public section

open Function MulOpposite

open scoped Pointwise

variable {F α β : Type*}

namespace Finset

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

open scoped Pointwise

open scoped Pointwise

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

section Instances

variable [DecidableEq α] [DecidableEq β]

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

section MulOneClass

variable [MulOneClass α]

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

end MulOneClass
end Instances
end Finset
end
