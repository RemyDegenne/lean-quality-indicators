namespace P2MW.S_CerednikDrinfeld_natCard_subideal_primeHeckeSet_eq_natCard_subgroup_dualPair_of_kernelIdealSet

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise

p2m_open

namespace CerednikDrinfeld

namespace E7b

p2m_open

noncomputable section

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

variable {a b : ℚ}

section Frame

variable {q' : ℕ} [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    {X₀ : WeierstrassCurve κ} [X₀.IsElliptic]
    {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]}
    {x y : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {W : WeierstrassCurve κ} [W.IsElliptic] {χ : X₀.toAffine.Point →+ W.toAffine.Point} {d : (ℍ[ℚ, a, b])ˣ}
    {W' : WeierstrassCurve κ} [W'.IsElliptic] {χ' : X₀.toAffine.Point →+ W'.toAffine.Point} {d' : (ℍ[ℚ, a, b])ˣ}
    {ℓ : ℕ}

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

attribute [scoped instance] VeluPkg.ell

p2m_reactivate

p2m_reactivate

namespace Hyp

variable (H : Hyp q' X₀ Λ θ x y W χ d W' χ' d' ℓ)

include H

theorem exists_isUnit_image_kernelIdealSet_eq (E : WeierstrassCurve κ) [E.IsElliptic]
    (χ₁ χ₂ : X₀.toAffine.Point →+ E.toAffine.Point)
    (h₁ : χ₁ ∈ WeierstrassCurve.rationalHomSet κ X₀ E) (h₁0 : χ₁ ≠ 0)
    (h₂ : χ₂ ∈ WeierstrassCurve.rationalHomSet κ X₀ E) (h₂0 : χ₂ ≠ 0) :
    ∃ v : ℍ[ℚ, a, b], IsUnit v ∧
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ E χ₁) = (· * v) '' (θ '' (WeierstrassCurve.kernelIdealSet κ X₀ E χ₂)) := by
  obtain ⟨σ₂, hσ₂, n₂, hn₂, hd₂⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ E h₂ h₂0
  have hu : σ₂.comp χ₁ ∈ WeierstrassCurve.rationalHomSet κ X₀ X₀ := WeierstrassCurve.comp_mem_rationalHomSet κ X₀ E X₀ h₁ hσ₂
  let ue : ↥(WeierstrassCurve.rationalEndSubring κ X₀) := ⟨σ₂.comp χ₁, Subring.subset_closure hu⟩
  have hsurj₁ : Function.Surjective χ₁ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ h₁ h₁0
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hn₂.le
  have hnpos : 0 < n := by rw [hn] at hn₂; exact_mod_cast hn₂
  have hσ₂0 : σ₂ ≠ 0 := by
    intro h0
    apply H.nsmul_id_ne_zero' X₀ hnpos
    ext P
    have e1 := hd₂.comp_left P
    rw [h0, hn] at e1
    have e2 : ((n : ℕ) : ℤ) • P = 0 := e1.symm
    rw [natCast_zsmul] at e2
    simpa using e2
  have hu0 : (σ₂.comp χ₁ : X₀.toAffine.Point →+ X₀.toAffine.Point) ≠ 0 := by
    intro h0; apply hσ₂0
    exact (AddMonoidHom.cancel_right hsurj₁).mp (h0.trans (AddMonoidHom.zero_comp χ₁).symm)
  obtain ⟨σu, hσu, t, m, hm, hdu, -⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id κ X₀ hu hu0
  let σue : ↥(WeierstrassCurve.rationalEndSubring κ X₀) := ⟨σu, Subring.subset_closure hσu⟩
  have hmul1 : θ ue * θ σue = ((m : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← map_mul]
    have : ue * σue = (m : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) := by
      apply Subtype.ext
      ext P
      show (σ₂.comp χ₁) (σu P) = ((m : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) : AddMonoid.End _) P
      exact (hdu.comp_right P).trans (by simp)
    rw [this, map_intCast]; norm_cast
  have hmul2 : θ σue * θ ue = ((m : ℚ) : ℍ[ℚ, a, b]) := by
    rw [← map_mul]
    have : σue * ue = (m : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) := by
      apply Subtype.ext
      ext P
      show σu ((σ₂.comp χ₁) P) = ((m : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) : AddMonoid.End _) P
      exact (hdu.comp_left P).trans (by simp)
    rw [this, map_intCast]; norm_cast
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hunit : IsUnit (θ ue) := by
    refine isUnit_iff_exists.mpr ⟨(m : ℚ)⁻¹ • θ σue, ?_, ?_⟩
    · rw [mul_smul_comm, hmul1, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hmQ]; rfl
    · rw [smul_mul_assoc, hmul2, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hmQ]; rfl
  have hn₂Q : (n₂ : ℚ) ≠ 0 := by exact_mod_cast hn₂.ne'
  refine ⟨(n₂ : ℚ)⁻¹ • θ ue, ?_, ?_⟩
  · rw [← QuaternionAlgebra.coe_mul_eq_smul]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hn₂Q)).map (algebraMap ℚ ℍ[ℚ, a, b])).mul hunit

  have key : ∀ ρ, ∀ hρ : ρ ∈ WeierstrassCurve.rationalHomSet κ E X₀,
      θ (compEnd' h₁ hρ) = θ (compEnd' h₂ hρ) * ((n₂ : ℚ)⁻¹ • θ ue) := by
    intro ρ hρ
    have hprod : compEnd' h₂ hρ * ue = (n₂ : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) * compEnd' h₁ hρ := by
      apply Subtype.ext
      ext P
      show ρ (χ₂ (σ₂ (χ₁ P))) = ((n₂ : ↥(WeierstrassCurve.rationalEndSubring κ X₀)) : AddMonoid.End _) (ρ (χ₁ P))
      exact (congrArg ρ (hd₂.comp_right (χ₁ P))).trans ((map_zsmul ρ n₂ _).trans (by simp))
    have e1 : θ (compEnd' h₂ hρ) * θ ue = ((n₂ : ℚ) : ℍ[ℚ, a, b]) * θ (compEnd' h₁ hρ) := by
      rw [← map_mul, hprod, map_mul, map_intCast]; norm_cast
    rw [mul_smul_comm, e1, QuaternionAlgebra.coe_mul_eq_smul, smul_smul, inv_mul_cancel₀ hn₂Q, one_smul]
  rw [H.image_kernelIdealSet_eq h₁, H.image_kernelIdealSet_eq h₂]
  ext w
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨θ (compEnd' h₂ hρ), ⟨ρ, hρ, rfl⟩, (key ρ hρ).symm⟩
  · rintro ⟨w₂, ⟨ρ, hρ, rfl⟩, rfl⟩
    exact ⟨ρ, hρ, key ρ hρ⟩

end Hyp
end Frame
end
end E7b
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_natCard_subideal_primeHeckeSet_eq_natCard_subgroup_dualPair_of_kernelIdealSet
