namespace OAI

namespace JointDickman

open Finset

theorem singularFactor_real_moment {C : ℝ} (hC : 0 ≤ C) (r : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℕ,
      (∑ j ∈ Ioc 0 U, singularFactor C j ^ r) ≤ K * U := by
  refine ⟨Real.exp ((⌈r⌉₊ : ℝ) * C * (1 + C) ^ (⌈r⌉₊ - 1)), Real.exp_pos _, ?_⟩
  intro U
  refine (sum_le_sum (fun j _ => ?_)).trans (singularFactor_nat_moment hC ⌈r⌉₊ U)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (singularFactor_one_le hC j) (Nat.le_ceil r)

end JointDickman
end OAI
