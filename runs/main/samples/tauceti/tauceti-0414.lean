public section

namespace TauCeti

open Filter NumberField

open scoped nonZeroDivisors NumberField

open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

theorem primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight
    (K : Type*) [Field K] [NumberField K] {E : Type*} [NormedAddCommGroup E]
    {w : IdealPrimePower K → E} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ A, ‖w A‖ ≤ C * higherPrimePowerWeight A) :
    (fun x ↦ primePowerSummatory K w x) =o[atTop] fun x : ℝ ↦ x :=
  (primePowerSummatory_isBigO_of_le_higherPrimePowerWeight K hC hw).trans_isLittleO
    isLittleO_sqrt_mul_log_sq

end TauCeti
end
