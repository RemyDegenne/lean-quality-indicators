@[expose] public section

namespace Erdos548

/-- Cuts `(l, k)` of words `l ∈ W` with `k ≤ m` whose prefix ends at a marked letter and whose
letter set satisfies `A`. -/
noncomputable def goodWordCuts {α : Type*} [DecidableEq α]
    (W : Finset (List α)) (m : ℕ) (N : α → Prop) (A : Finset α → Prop) :
    Finset (List α × ℕ) := by
  classical
  exact (W ×ˢ Finset.range (m + 1)).filter
    (fun p => MarkedEnd N (p.1.take p.2) ∧ A (p.1.take p.2).toFinset)

end Erdos548
end
