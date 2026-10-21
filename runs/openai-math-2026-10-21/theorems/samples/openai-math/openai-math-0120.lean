namespace OAI

section

namespace Erdos3

theorem forecastJacobian_mass_exp_bound {κ Pκ M mass : ℝ}
    (hκ : 0 ≤ κ) (hκbound : κ ≤ Real.exp Pκ) (hmass : mass ≤ Real.exp M) :
    κ * mass ≤ Real.exp (Pκ + M) := by
  calc
    κ * mass ≤ κ * Real.exp M := mul_le_mul_of_nonneg_left hmass hκ
    _ ≤ Real.exp Pκ * Real.exp M :=
      mul_le_mul_of_nonneg_right hκbound (Real.exp_nonneg _)
    _ = Real.exp (Pκ + M) := (Real.exp_add Pκ M).symm

end Erdos3
end
end OAI
