@[expose] public section

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  [Ring R]
  {Γ''₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ''₀]
  {v : AddValuation R Γ₀} {v₁ : AddValuation R Γ₀}
  {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  Valuation.IsEquiv.eq_iff h

end IsEquiv
end AddValuation
end
end
