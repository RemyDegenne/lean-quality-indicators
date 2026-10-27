@[expose] public section

namespace Lean4LPD

open Finset

/-- The saturating family: `N m g := C(g,m) · (∏_{j=1}^{m} c j) · M`. -/
noncomputable def satLadder {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) :
    WeightedLadder c M where
  N m g := (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M
  nonneg m g := by
    have : (0 : ℝ) ≤ ∏ j ∈ Icc 1 m, c j := Finset.prod_nonneg fun j _ => hc j
    positivity
  reservoir g := by simp
  init m hm := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  step m g hm := by
    match m with
    | 0 => omega
    | (m + 1) =>
      have hprod : ∏ j ∈ Icc 1 (m + 1), c j = (∏ j ∈ Icc 1 m, c j) * c (m + 1) :=
        Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) c
      have hpascal : ((g + 1).choose (m + 1) : ℝ) = (g.choose m : ℝ) + (g.choose (m + 1) : ℝ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      simp only [Nat.add_sub_cancel]
      rw [hprod, hpascal]
      ring_nf
      exact le_refl _

end Lean4LPD
end
