@[expose] public section

noncomputable section

open Finset Function

variable {α M N R : Type*}

namespace Finsupp

section Option

section Zero

variable [Zero M]

/-- `Finsupp`s from `Option` are equivalent to
pairs of an element and a `Finsupp` on the original type. -/
@[simps]
noncomputable
def optionEquiv : (Option α →₀ M) ≃ M × (α →₀ M) where
  toFun P := (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

end Zero
end Option
end Finsupp
end
end
