@[expose] public section

universe v

variable {α : Type*} {β : Type v} {γ δ : Type*}

namespace Multiset

section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

@[simp]
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [SProd.sprod, product]

end Product
end Multiset
end
