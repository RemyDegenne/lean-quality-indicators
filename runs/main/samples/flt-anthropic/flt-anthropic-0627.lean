namespace P2MW.S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve Polynomial

open scoped Polynomial.Bivariate

universe u

namespace S13MulDatum

section Degree

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]

scoped instance torsMulSemiringAction (n : ℕ) :
    MulSemiringAction (Multiplicative (tors W n)) (W⁄F).FunctionField :=
  MulSemiringAction.compHom _ (torsAct W n)

scoped instance torsFaithful (n : ℕ) : FaithfulSMul (Multiplicative (tors W n)) (W⁄F).FunctionField where
  eq_of_smul_eq_smul h := torsAct_injective W n (AlgEquiv.ext h)

theorem fieldRange_eq_fixed {n : ℕ} (hn : (n : F) ≠ 0) :
    (mulPull W F n).fieldRange.toSubfield
      = FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField ∧
    Module.finrank (mulPull W F n).fieldRange (W⁄F).FunctionField = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  haveI : Finite (tors W n) := finite_tors W hn
  letI : Fintype (tors W n) := Fintype.ofFinite _
  letI : Fintype (Multiplicative (tors W n)) := Fintype.ofFinite _
  set A : Subfield (W⁄F).FunctionField := (mulPull W F n).fieldRange.toSubfield with hA
  set B : Subfield (W⁄F).FunctionField :=
    FixedPoints.subfield (Multiplicative (tors W n)) (W⁄F).FunctionField with hB
  have hAB : A ≤ B := fieldRange_le_fixed W hn
  obtain ⟨hfinA, hleA⟩ :=
    WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le (K := F) W (mulGood_of_natCast_ne_zero W hn)
  rw [Int.natAbs_natCast] at hleA
  have hfA : Module.finrank A (W⁄F).FunctionField
      = Module.finrank (mulPull W F n).fieldRange (W⁄F).FunctionField := finrank_toSubfield_eq _
  have hposA : 0 < Module.finrank A (W⁄F).FunctionField := by rw [hfA]; exact Module.finrank_pos
  have hcard : Fintype.card (Multiplicative (tors W n)) = n ^ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Multiplicative.toAdd : Multiplicative (tors W n) ≃ _),
      natCard_tors W hn]
  have hfB : Module.finrank B (W⁄F).FunctionField = n ^ 2 := by
    rw [hB, FixedPoints.finrank_eq_card, hcard]
  have htower := Subfield.relfinrank_mul_finrank_top hAB
  rw [hfB] at htower
  have hsqpos : 0 < n ^ 2 := by positivity
  have hrel_le : Subfield.relfinrank A B ≤ 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hsqpos
    rw [htower, one_mul, hfA]; exact hleA
  have hrel_pos : 0 < Subfield.relfinrank A B := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at htower
    omega
  have hrel : Subfield.relfinrank A B = 1 := le_antisymm hrel_le hrel_pos
  have hEq : A = B := le_antisymm hAB (Subfield.relfinrank_eq_one_iff.mp hrel)
  refine ⟨hEq, ?_⟩
  rw [← hfA, hEq, hfB]

end Degree
end S13MulDatum
end
end P2MW.S_WeierstrassCurve_Affine_exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul
