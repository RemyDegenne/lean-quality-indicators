@[expose] public section

namespace Complexity

attribute [instance] TM.decEq TM.finQ

attribute [instance] NTM.decEq NTM.finQ

namespace NTM

variable {n : ℕ}

theorem AllPathsHaltIn.mono {tm : NTM n} {T T' : ℕ → ℕ} (hle : ∀ m, T m ≤ T' m)
    (h : tm.AllPathsHaltIn T) : tm.AllPathsHaltIn T' := by
  intro x choices'
  have heq := tm.trace_mono (hle x.length)
    (choices := fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
    (choices' := choices') (c := tm.initCfg x) (fun i => rfl)
    (h x fun i => choices' ⟨i.val, lt_of_lt_of_le i.isLt (hle x.length)⟩)
  rw [heq]
  exact h x _

end NTM
end Complexity
end
