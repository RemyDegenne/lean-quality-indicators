namespace P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open scoped MatrixGroups

namespace P2MKcORB

section Matrices

variable {M : ℕ} [NeZero M]

theorem mv_ST (v : Fin 2 → ZMod M) :
    mv (ModularGroup.S * ModularGroup.T) v = ![-v 1, v 0 + v 1] := by
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ext i
  rw [mv_apply]
  fin_cases i <;> simp [hST]

end Matrices
end P2MKcORB
end P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
