@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace CycleModelAux

section CycleGraph

variable {m : ℕ}

theorem cycleNext_val' (v : Fin m) :
    (cycleNext v).val = if v.val + 1 = m then 0 else v.val + 1 := by
  change (v.val + 1) % m = _
  by_cases h : v.val + 1 = m
  · rw [ite_eq_left h, h, Nat.mod_self]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega : v.val + 1 < m)]

end CycleGraph
end CycleModelAux
end TriangleInflation.Graph
end
