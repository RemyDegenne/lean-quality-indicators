@[expose] public section

lemma ramanujanSum_norm_le_totient (n : ℕ) [NeZero n] (t : ℤ) :
    ‖ramanujanSum n t‖ ≤ (Nat.totient n : ℝ) := by
  calc
    ‖ramanujanSum n t‖ = ‖∑ a : (ZMod n)ˣ, ZMod.stdAddChar (a.val * (t : ZMod n))‖ := rfl
    _ ≤ ∑ a : (ZMod n)ˣ, ‖ZMod.stdAddChar (a.val * (t : ZMod n))‖ := norm_sum_le _ _
    _ = ∑ _ : (ZMod n)ˣ, (1 : ℝ) := Finset.sum_congr rfl fun a _ => by simp
    _ = (Nat.totient n : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul, ZMod.card_units_eq_totient]

end
