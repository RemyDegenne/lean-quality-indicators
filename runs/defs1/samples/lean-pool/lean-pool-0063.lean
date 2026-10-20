@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **Output accumulator.** The output tape holds exactly the bits `ys`
    (cells `1..|ys|`, after the `▷` at cell 0), all cells beyond are blank,
    and the head is parked on the first blank — ready to append. -/
def OutAcc (ys : List Bool) (out : Tape) : Prop :=
  out.head = ys.length + 1 ∧
  out.cells 0 = Γ.start ∧
  (∀ i, (h : i < ys.length) → out.cells (i + 1) = Γ.ofBool ys[i]) ∧
  (∀ j, ys.length + 1 ≤ j → out.cells j = Γ.blank)

end TM
end Complexity
end
