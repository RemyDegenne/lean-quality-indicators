@[expose] public section

open Filter Asymptotics

variable (R : RamanujanTau)

lemma E4_fiber_subset_pos_neg (X : ℝ) (hX : 4 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | (x, u) ∈ E4Set X} ⊆
    {u : ℤ | 0 < u ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} ∪
    {u : ℤ | u < 0 ∧ (↑u : ℝ) ^ 2 ≥ 5 * (↑↑x : ℝ) ^ 22 - 4 * X ∧
              (↑u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X} := by
  intro u hu
  have hbounds := E4_set_D_bounds X (x, u) hu
  have h5pos := five_x22_sub_4X_pos X hX x hx
  have hinterval := u_sq_in_interval X x u hbounds.2
  have hne : u ≠ 0 := u_ne_zero_of_fiber X hX x hx u hinterval.1 h5pos
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    exact ⟨hneg, hinterval.1, hinterval.2⟩
  · left
    exact ⟨hpos, hinterval.1, hinterval.2⟩

end
