@[expose] public section

open Function

universe u

variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv

@[simp, grind =]
theorem prodComm_apply {α β} (x : α × β) : prodComm α β x = x.swap :=
  rfl

end Equiv
end
