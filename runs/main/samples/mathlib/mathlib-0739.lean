@[expose] public section

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

section Basic

section Monoid

variable [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  (v : AddValuation R Γ₀)

section

variable (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)

variable (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
theorem toValuation_apply (r : R) :
    toValuation v r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

end
end Monoid
end Basic
end AddValuation
end
end
