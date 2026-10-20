namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane hiding I

open ModularCurve HahnSeries CongruenceSubgroup WeierstrassCurve WeierstrassCurve.Affine

open scoped MatrixGroups ModularForm

namespace R4TateModelKHb

section Abscissa

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)

variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ) (p n : ℕ) [NeZero p] [NeZero n] (hpn : p ∣ n)

variable (hle : Γgl N₀ H ≤ ((Gamma1 n ⊓ Gamma0 (p * n) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))

theorem Xc_def (x : LaurentSeries L) : Xc x = x + HahnSeries.C ((12 : L)⁻¹) := rfl

end Abscissa
end R4TateModelKHb
end
end P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
