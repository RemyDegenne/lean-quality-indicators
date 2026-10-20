public section

variable {m n k : ℕ} {p q : ℕ → Prop}

namespace Nat

section Find

variable [DecidablePred p] (H : ∃ n, p n)

/-- Find the smallest `n` satisfying `p n`. Returns a subtype. -/
protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)

end Find
end Nat
end
