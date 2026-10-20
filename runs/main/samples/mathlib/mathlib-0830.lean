@[expose] public section

open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

@[inherit_doc]
infixl:25 " ≃ " => Equiv

namespace Equiv

@[simp] theorem arrowCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := rfl

end Equiv
end
