namespace P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH

set_option autoImplicit false

open UpperHalfPlane MeasureTheory

open scoped MatrixGroups Modular ComplexConjugate Manifold Topology Pointwise

namespace PeterssonRieszHSol

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

scoped instance finiteIndex_sup_zpowers_neg_one : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
  Subgroup.finiteIndex_of_le (K := Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (H := Γ) le_sup_left

scoped instance finiteDimensional_S2 : FiniteDimensional ℂ (S2 Γ) :=
  CuspForm.finiteDimensional_of_isArithmetic ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2

theorem petersson_smul_left_apply (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) (τ : ℍ) :
    petersson k (c • f) g τ = conj c * petersson k f g τ := by
  simp only [petersson, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

end PeterssonRieszHSol
end P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH
