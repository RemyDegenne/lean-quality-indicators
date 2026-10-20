namespace P2MW.S_ModularCurve_PDPairing_index_Gamma_four

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PDPairing

namespace TD

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Assembly

open CongruenceSubgroup

variable {R : Type*} [CommRing R]

theorem pairF_res_cores_normal {Φ Γ' : Subgroup SL(2, ℤ)} (hΦΓ : Φ ≤ Γ') [Φ.FiniteIndex] [Γ'.FiniteIndex]
    [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ)
    (z : Additive Φ →+ R) (y : Additive Γ' →+ R) (hz : IsPar Φ z) (hy : IsPar Γ' y) :
    pairF Φ (res hΦΓ (cores hΦΓ z)) (res hΦΓ y) = (Φ.relIndex Γ' : R) * pairF Φ z (res hΦΓ y) := by
  classical
  set K : Subgroup Γ' := Φ.subgroupOf Γ' with hK
  haveI : Fintype (Γ' ⧸ K) := Fintype.ofFinite _
  let eK : K ≃* Φ := Subgroup.subgroupOfEquivOfLe hΦΓ
  let xK : Additive K →+ R := z.comp (MonoidHom.toAdditive eK.toMonoidHom)
  have hcor : ∀ g : Γ', (cores hΦΓ z) (Additive.ofMul g) =
      coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q) xK g := by
    intro g; rw [coresFun_eq]; rfl

  have htriv : ∀ (g : Φ) (q : Γ' ⧸ K), (Subgroup.inclusion hΦΓ g)⁻¹ • q = q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H s =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      rw [hK, Subgroup.mem_subgroupOf]
      have h := hnorm s⁻¹ g
      simp only [Subgroup.coe_inv, inv_inv] at h
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h

  have hsum : res hΦΓ (cores hΦΓ z) =
      ∑ q : Γ' ⧸ K, z.comp (MonoidHom.toAdditive (normConj hnorm (Quotient.out q)).toMonoidHom) := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    rw [AddMonoidHom.finsetSum_apply]
    show (cores hΦΓ z) (Additive.ofMul (Subgroup.inclusion hΦΓ g)) = _
    rw [hcor, coresFun]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    show z (Additive.ofMul (eK (gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g)))) =
      z (Additive.ofMul (normConj hnorm q.out g))
    congr 2
    apply Subtype.ext
    show (((gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g) : K) : Γ') :
      SL(2, ℤ)) = _
    rw [coe_gam, htriv, coe_normConj]
    rfl
  rw [hsum, pairF_sum_left]
  have hterm : ∀ q : Γ' ⧸ K,
      pairF Φ (z.comp (MonoidHom.toAdditive (normConj hnorm q.out).toMonoidHom)) (res hΦΓ y) =
        pairF Φ z (res hΦΓ y) := by
    intro q
    set s : Γ' := q.out
    have hy' : (res hΦΓ y).comp (MonoidHom.toAdditive (normConj hnorm s).toMonoidHom) = res hΦΓ y := by
      refine AddMonoidHom.ext fun g => ?_
      obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
      show y (Additive.ofMul (Subgroup.inclusion hΦΓ (normConj hnorm s g))) =
        y (Additive.ofMul (Subgroup.inclusion hΦΓ g))
      have : Subgroup.inclusion hΦΓ (normConj hnorm s g) = s⁻¹ * Subgroup.inclusion hΦΓ g * s :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; rfl)
      rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
      ring
    have ht := pairF_transport hΦ1 hΦ1 (normConj hnorm s)
      (((s : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (fun g => by
        rw [coe_normConj]
        have h1 : ((s : SL(2, ℤ)))⁻¹ * (g : SL(2, ℤ)) = ((s : SL(2, ℤ))⁻¹ * g * s) * (s : SL(2, ℤ))⁻¹ := by group
        have h2 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) h1
        simpa only [Matrix.SpecialLinearGroup.coe_mul] using h2)
      z (res hΦΓ y) hz (isPar_res hΦΓ y hy)
    rw [hy'] at ht
    exact ht
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Assembly
end TD
end PDPairing
end ModularCurve
end P2MW.S_ModularCurve_PDPairing_index_Gamma_four
