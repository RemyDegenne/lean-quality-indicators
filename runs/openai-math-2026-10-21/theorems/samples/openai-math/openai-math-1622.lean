namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset

open PrimeAbel

theorem endpoint_difference {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (lc rc : Bool) : |intervalSum lc rc a b - reciprocalPrimes a b| ≤ 2 / a := by
  classical
  have hw : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  rw [intervalSum, reciprocal_eq_core ha.le hab, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        |(if intervalGuard lc rc a b (n : ℝ) then (n : ℝ)⁻¹ else 0) -
          (if a < (n : ℝ) then (n : ℝ)⁻¹ else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        ((if (n : ℝ) = a then a⁻¹ else 0) + (if (n : ℝ) = b then a⁻¹ else 0)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hp : n.Prime := (Nat.mem_primesLE.mp hn).2
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hp.pos
      have hnw : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
      have hnb : (n : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha.le hab)).mp (Nat.mem_primesLE.mp hn).1
      by_cases hna : (n : ℝ) = a
      · have hd := selection_difference_bound (intervalGuard lc rc a b (n : ℝ)) (a < (n : ℝ)) hnw
        calc
          _ ≤ (n : ℝ)⁻¹ := hd
          _ ≤ _ := by rw [hna]; split_ifs <;> simp_all
      · by_cases hneqb : (n : ℝ) = b
        · calc
            _ ≤ (n : ℝ)⁻¹ := selection_difference_bound _ _ hnw
            _ ≤ a⁻¹ := by rw [hneqb]; exact inv_anti₀ ha hab
            _ = _ := by rw [ite_eq_right hna, ite_eq_left hneqb, zero_add]
        · have hguard : intervalGuard lc rc a b (n : ℝ) ↔ a < (n : ℝ) := by
            have hne : a ≠ (n : ℝ) := Ne.symm hna
            cases lc <;> cases rc <;> simp_all [intervalGuard, le_iff_lt_or_eq]
          simp [hguard, hna, hneqb]
    _ ≤ a⁻¹ + a⁻¹ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (fiber_sum_le _ _ hw) (fiber_sum_le _ _ hw)
    _ = 2 / a := by ring

end ErdosPrimeInputs.PrimeEndpoints
end Erdos970
end OAI
