@[expose] public section

namespace Lean4GlCoalgebras

open Player

theorem Player.ne_A_iff_eq_B {p} : p ≠ A ↔ p = B := by cases p <;> simp

end Lean4GlCoalgebras
end
