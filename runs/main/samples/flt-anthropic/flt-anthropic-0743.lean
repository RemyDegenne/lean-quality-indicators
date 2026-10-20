open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

noncomputable section

theorem cuspWidthOfDenom_gcd (N d : ℕ) :
    cuspWidthOfDenom N (Nat.gcd d N) = cuspWidthOfDenom N d := by
  unfold cuspWidthOfDenom
  rw [gcd_sq_gcd_left]

end
end ModularCurve
