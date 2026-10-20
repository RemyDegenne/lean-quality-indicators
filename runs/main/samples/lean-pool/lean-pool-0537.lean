@[expose] public section

open Metric Set

namespace Schoenflies

variable {u a b c p q z w : Plane} {s t : ℝ} {L : List Piece}

theorem nondeg_of_hgt_ne {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) : P.Nondeg := by
  intro hEq
  exact h (by rw [hEq])

end Schoenflies
end
