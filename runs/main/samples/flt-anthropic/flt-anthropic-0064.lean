namespace P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral

noncomputable section

open Polynomial IntermediateField AlgebraicCurve

namespace W8O

section PurelyInseparable

variable {K M E : Type*} [Field K] [Field M] [Field E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional M E] [IsPurelyInseparable M E]
  (p : ℕ) [Fact p.Prime] [CharP E p] [CharP M p] {r : ℕ}
  (hrange : (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange)

include hrange in
omit [Algebra K M] [IsScalarTower K M E] in

theorem ramificationIndex_eq (w : Place K E) : w.ramificationIndex M = p ^ r := by
  have hprime : p.Prime := Fact.out
  apply le_antisymm
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hπ0 : (π : E) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    have hθπ0 : theta p hrange (π : E) ≠ 0 := theta_ne_zero p hrange hπ0
    have hord : w.ord (algebraMap M E (theta p hrange (π : E))) = (p ^ r : ℕ) := by
      rw [algebraMap_theta, ord_npow, w.ord_coe_irreducible hπ, mul_one]
    have := Place.ramificationIndex_le_ord (F := M) w hθπ0
      (by rw [hord]; exact_mod_cast pow_pos hprime.pos r)
    rw [hord] at this
    exact_mod_cast this
  · obtain ⟨m, hm0, hm⟩ := Place.exists_ord_eq_ramificationIndex (F := M) w
    obtain ⟨x, rfl⟩ := theta_surjective p hrange m
    rw [algebraMap_theta, ord_npow] at hm
    have hpos := Place.ramificationIndex_pos (F := M) w

    have hx1 : 1 ≤ w.ord x := by
      by_contra hlt
      have : (↑(p ^ r) : ℤ) * w.ord x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      omega
    have : (↑(p ^ r) : ℤ) * 1 ≤ ↑(p ^ r) * w.ord x :=
      mul_le_mul_of_nonneg_left hx1 (by positivity)
    have h' : ((p ^ r : ℕ) : ℤ) ≤ (w.ramificationIndex M : ℤ) := by rw [← hm]; linarith
    exact_mod_cast h'

end PurelyInseparable
end W8O
end
end P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos
