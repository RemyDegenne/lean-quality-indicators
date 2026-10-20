@[expose] public section

open Nat Set

open Cardinal

noncomputable section

namespace Cardinal

variable {c : ℝ} {f g : ℕ → Bool} {n : ℕ}

theorem cantorFunctionAux_zero (f : ℕ → Bool) : cantorFunctionAux c f 0 = cond (f 0) 1 0 := by
  cases h : f 0 <;> simp [h]

end Cardinal
end
end
