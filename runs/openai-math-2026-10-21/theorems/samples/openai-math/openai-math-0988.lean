namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators

theorem sum_all_schedule_bounds_le (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) :
    (∑ n : Fin 7, ∑ s : Fin n.val → Fin 5,
      if 3 ≤ score s then A ^ n.val / q ^ score s else 0) ≤
        19531 * (max 1 A) ^ 6 / q ^ 3 := by
  classical
  calc
    _ ≤ ∑ n : Fin 7, (5 : ℝ) ^ n.val * ((max 1 A) ^ 6 / q ^ 3) := by
      apply Finset.sum_le_sum
      intro n _
      exact sum_schedule_bounds_le A q hA hq n.val (by omega)
    _ = _ := by rw [← Finset.sum_mul, schedule_count]; ring

end Balanced.ReuseSchedule
end OAI
