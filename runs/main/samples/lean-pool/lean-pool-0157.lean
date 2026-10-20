@[expose] public section

namespace Complexity

open Complexity.TM

variable {k : ℕ}

variable {M : TM k} {Y : ℕ → List Bool} {inp₀ junkT : Tape} {v H : ℕ}

@[simp] theorem iterFamily_app (i : ℕ) (j : Fin (k + 2)) :
    iterFamily M Y inp₀ junkT v H i (appIdx j) = TM.applyPre M (Y i) inp₀ j := by
  rw [iterFamily]
  rw [dite_eq_left (appIdx_middle j)]
  congr 1
  exact placeWorkCoord_placeWorkIdx 3 0 j

end Complexity
end
