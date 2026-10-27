public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.TwoRankLowerBound.Helpers

open scoped BigOperators Classical

theorem finiteOrderEigenprojection_apply_of_eigenvector {V : Type*} [AddCommGroup V]
    [Module ℂ V] (period : ℕ) (periodUnit eigenvalue : ℂˣ)
    (hunit : (periodUnit : ℂ) = period) (operator : Module.End ℂ V) {x : V}
    (hx : operator x = (eigenvalue : ℂ) • x) :
    finiteOrderEigenprojection period periodUnit eigenvalue operator x = x := by
  have hp : ∀ k : ℕ, (((↑eigenvalue⁻¹ : ℂ) • operator) ^ k) x = x := by
    intro k
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk, LinearMap.smul_apply, hx, smul_smul,
        Units.inv_mul, one_smul]
  change (↑periodUnit⁻¹ : ℂ) •
    ((∑ k ∈ Finset.range period, ((↑eigenvalue⁻¹ : ℂ) • operator) ^ k) x) = x
  rw [LinearMap.sum_apply]
  simp only [hp, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hunit, Units.inv_mul, one_smul]

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
end
