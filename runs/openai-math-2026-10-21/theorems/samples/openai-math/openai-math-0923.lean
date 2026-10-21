namespace OAI

namespace JointDickman

open Finset Classical

theorem uniformCell_indicator_sum (a δ x : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    (∑ r ∈ range k, if x ∈ Set.Ioc (a+r*δ) (a+(r+1)*δ) then (1 : ℝ) else 0) =
      if x ∈ Set.Ioc a (a+k*δ) then 1 else 0 := by
  have he (r : ℕ) : (if x ∈ Set.Ioc (a+r*δ) (a+(r+1)*δ) then (1 : ℝ) else 0) =
      (if x ≤ a+(r+1)*δ then 1 else 0)-(if x ≤ a+r*δ then 1 else 0) :=
    intervalIndicator_eq_sub (by linarith) x
  simp_rw [he]
  have hs := sum_range_sub (fun r : ℕ => if x ≤ a+(r : ℝ)*δ then (1 : ℝ) else 0) k
  simp only [Nat.cast_add,Nat.cast_one] at hs
  rw [hs]
  simp only [Nat.cast_zero,zero_mul,add_zero]
  exact (intervalIndicator_eq_sub (le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg k) hδ)) x).symm

end JointDickman
end OAI
