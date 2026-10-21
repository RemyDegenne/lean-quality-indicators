namespace OAI

namespace FiniteFactor

open MeasureTheory Filter Finset

open scoped ENNReal Topology

noncomputable section

theorem sourceCutoff_tail_bound (s : ℕ) :
    (∑' n : ℕ, 1 / ((sourceStageState (s+n)).K : ℝ)) ≤
      2 / ((sourceStageState s).K : ℝ) := by
  let b (n : ℕ) : ℝ := (1 / ((sourceStageState s).K : ℝ)) * (1/2 : ℝ)^n
  have hb : Summable b := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left _
  have hle (n : ℕ) : 1 / ((sourceStageState (s+n)).K : ℝ) ≤ b n := by
    have hh : (2 : ℝ)^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K :=
      by exact_mod_cast sourceCutoff_ge_shift s n
    have hp : (0 : ℝ) < 2^n * (sourceStageState s).K := mul_pos (by positivity) (sourceCutoff_pos s)
    have ht := one_div_le_one_div_of_le hp hh
    simpa [b, one_div_pow, mul_comm, mul_left_comm] using ht
  calc
    _ ≤ ∑' n, b n := (hb.of_nonneg_of_le (fun _ => by positivity) hle).tsum_le_tsum hle hb
    _ = 2 / ((sourceStageState s).K : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)]
      ring

end
end FiniteFactor
end OAI
