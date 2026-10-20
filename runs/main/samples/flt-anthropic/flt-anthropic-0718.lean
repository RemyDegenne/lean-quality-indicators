namespace P2MW.S_WeierstrassCurve_galoisRep_supersingularShapeAt

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

open scoped NumberField Pointwise

p2m_reactivate

set_option autoImplicit false

open scoped Pointwise

namespace AlgEquiv p2m_export "AlgEquiv" "ext coe_inv restrictNormal mul_apply trans restrictNormal_commutes ofBijective restrictNormalHom restrictScalars mk ofRingEquiv isIntegral_iff commutes apply_symm_apply restrictNormalHom_surjective symm one_apply isAlgebraic" end AlgEquiv

namespace ValuationSubring

p2m_open

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

p2m_reactivate

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

theorem tameChar_mul {A : ValuationSubring L} {σ τ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) (hτ : τ ∈ A.decompositionSubgroup K) (z : L) :
    A.tameChar (σ * τ) z = A.tameChar σ z * A.tameChar τ z := by
  by_cases hz : z = 0
  · subst hz; simp
  have hD : σ ∈ A.decompositionSubgroup K := inertiaSubgroupIn_le_decompositionSubgroup K A hσ
  have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
  have e : (σ * τ) z * z⁻¹ = σ (τ z * z⁻¹) * (σ z * z⁻¹) := by
    rw [AlgEquiv.mul_apply, map_mul, map_inv₀, mul_assoc, inv_mul_cancel_left₀ hσz]
  have hmem : σ (τ z * z⁻¹) ∈ A :=
    (apply_mem_iff_of_mem_decompositionSubgroup hD _).mpr (apply_mul_inv_mem hτ z)
  rw [tameChar, e, A.residueOrZero_mul hmem (apply_mul_inv_mem hD z),
    residueOrZero_apply_of_mem_inertiaSubgroupIn hσ (apply_mul_inv_mem hτ z), mul_comm]
  rfl

end IsAlgebraic
end ValuationSubring
end AlgEquiv
end P2MW.S_WeierstrassCurve_galoisRep_supersingularShapeAt
