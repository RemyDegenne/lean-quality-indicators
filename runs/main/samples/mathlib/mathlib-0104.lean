@[expose] public section

open Function

variable {α β γ δ : Sort*}

namespace PProd

@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  rfl

end PProd
end
