@[expose] public section

theorem Nat.gt_and_neq_succ_gt_succ : ∀ (n m : ℕ), n < m → m ≠ n + 1 → n + 1 < m := by
  intros n m h₁ h₂
  grind

end
