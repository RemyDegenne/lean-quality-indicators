@[expose] public section

noncomputable section

namespace Erdos367

open Finsupp Nat

theorem pell_identity (j : ℕ) : pellX j ^ 2 - 8 * pellY j ^ 2 = 1 := by
  induction j with
  | zero => simp
  | succ n ih => simp only [pellX_succ, pellY_succ]; nlinarith

end Erdos367
end
end
