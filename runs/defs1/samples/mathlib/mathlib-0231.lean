@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

section

variable {ι : Type*} [Preorder ι] (i₀ i₁ i₂ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂)

/-- Variant of `twoδ₁Toδ₀` for preorders. -/
abbrev twoδ₁Toδ₀' :
    mk₁ (homOfLE (hi₀₁.trans hi₁₂)) ⟶ mk₁ (homOfLE hi₁₂) :=
  twoδ₁Toδ₀ (homOfLE hi₀₁) _ _ rfl

end
end ComposableArrows
end CategoryTheory
end
