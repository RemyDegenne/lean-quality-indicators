public section

namespace CFSG.Sporadic.Ly

theorem countIn_fold (lo : ℕ) (f : ℕ → Bool) (m : ℕ) :
    Nat.fold m (fun k _ acc => if f (lo + k) then acc + 1 else acc) 0 =
      ((Finset.Ico lo (lo + m)).filter (fun i => f i = true)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlo : lo + (m + 1) = lo + m + 1 := rfl
    rw [Nat.fold_succ, ih, Finset.card_filter, Finset.card_filter, hlo,
      Finset.sum_Ico_succ_top (Nat.le_add_right lo m)]
    by_cases h : f (lo + m) = true <;> simp [h]

end CFSG.Sporadic.Ly
end
