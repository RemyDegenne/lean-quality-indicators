@[expose] public section

open Finset

open scoped BigOperators

namespace CriticalPortraits

open Finset

open scoped BigOperators

variable {d m : ℕ}

lemma level_lt_of_val_lt [NeZero (d * m)] {x y : ZMod (d * m)}
    (hfib : x.val % m = y.val % m) (h : x.val < y.val) : x.val / m < y.val / m := by
  rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hfib).mp h.le) with hlt | heq
  · exact hlt
  · exact absurd (congrArg ZMod.val (level_injOn_fiber hfib heq)) (Nat.ne_of_lt h)

end CriticalPortraits
end
