namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

open Matrix

namespace BinaryCoordinateSweeps.Density

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma phaseAverage_psd (n : ℕ) (r : A → ℝ) : (phaseAverage n r).PosSemidef := by
  apply Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ (fun θ _ => rankOne_psd _))
  exact inv_nonneg.mpr (pow_nonneg (by exact_mod_cast Nat.zero_le (n+1)) _)

end BinaryCoordinateSweeps.Density
end
end
end OAI
