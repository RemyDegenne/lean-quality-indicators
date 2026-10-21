namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end IndependentSetsGames.Foundations.PCP.RawInitialMachineCleanup
end OAI
