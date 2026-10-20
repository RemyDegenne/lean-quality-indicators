@[expose] public section

namespace Complexity

variable {n : ℕ}

namespace TM

theorem transitionTape_eq_self {t : Tape} (hread : t.read ≠ Γ.start) :
    transitionTape t = t := by
  unfold transitionTape Tape.writeAndMove
  rw [toΓ_readBackWrite_of_ne_start hread]
  simp only [idleDir, hread, ↓reduceIte, Tape.move, Tape.write]
  split
  · rfl
  · simp only [Tape.read, Function.update_eq_self]

end TM
end Complexity
end
