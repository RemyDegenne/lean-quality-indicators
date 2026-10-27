public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin.MS93.S36

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem coreData_one (h : PUHyp M T L) {k : ℕ} {φ : MulAut ↥T} {Y Y' K K' : Subgroup G}
    (hφ : EndSide M T L k φ Y) (hφ' : EndSide M T L k φ⁻¹ Y')
    (hK : ⁅Y, pCoreOf 2 M⁆ ≤ K ∧ K ≤ tImage φ (Uq M T L) ∧
      K ≤ Subgroup.centralizer (M : Set G) ∧ K ⊓ tImage φ (Uq M T L ⊓ Zq M L) = ⊥)
    (hK' : ⁅Y', pCoreOf 2 M⁆ ≤ K' ∧ K' ≤ tImage φ⁻¹ (Uq M T L) ∧
      K' ≤ Subgroup.centralizer (M : Set G))
    (hside : (tImage φ (pCoreOf 2 M)).relIndex (normalClosureIn M Y) ≤
      (tImage φ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Y')) (hk : k = 1) :
    CoreData M T L k φ Y Y' K K' := by
  obtain ⟨hYK, hKU, hKc, hKinf⟩ := hK
  obtain ⟨hYK', hKU', hKc'⟩ := hK'
  have hUT : Uq M T L ≤ T := h.Uq_le_Xq.trans ((Xq_le_pCoreOf M).trans h.pCore_le)
  have hcentZ : ∀ {θ : MulAut ↥T} {J : Subgroup G}, J ≤ tImage θ (Uq M T L) →
      J ≤ Subgroup.centralizer (M : Set G) → J ≤ Z0q M T := by
    intro θ J hJU hJc x hx
    have hxT : x ∈ T := tImage_le θ _ (hJU hx)
    have hx2 : x ^ 2 = 1 := by
      obtain ⟨t, ht, rfl⟩ := mem_tImage.1 (hJU hx)
      have h2 : t ^ 2 = 1 := Subtype.ext (h.isElemAbelian_Uq.2 _ ht)
      rw [← Subgroup.coe_pow, ← map_pow, h2, map_one]
      rfl
    have hxZ : x ∈ omegaOneCenterOf T := by
      refine Subgroup.subset_closure ⟨⟨hxT, ?_⟩, hx2⟩
      exact Subgroup.centralizer_le h.le (hJc hx)
    exact le_normalClosureIn ((PU.omegaOneCenterOf_le T).trans h.le) hxZ
  have hcentn : ∀ {J : Subgroup G}, J ≤ Subgroup.centralizer (M : Set G) →
      M ≤ Subgroup.normalizer (J : Set G) := by
    intro J hJ m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff.1 (hJ hx) m hm, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 := Subgroup.mem_centralizer_iff.1 (hJ hx) m hm
      have e1 : m * x * m⁻¹ = x := by
        have h2 : m * (m * x * m⁻¹) = m * x := by
          rw [h1]
          group
        exact mul_left_cancel h2
      rw [e1] at hx
      exact hx
  have hcentL : ∀ {J : Subgroup G}, J ≤ Subgroup.centralizer (M : Set G) →
      L ≤ Subgroup.centralizer (J : Set G) := by
    intro J hJ
    rw [← Subgroup.le_centralizer_iff]
    exact hJ.trans (Subgroup.centralizer_le h.L_le)
  refine
    { crit' := hφ.crit'
      index := hφ.index
      Yp_ge := hφ.Y_ge
      Yp_le := hφ.Y_le
      Yp_comm := hYK
      not_le := hφ.not_le
      comm_le := hφ.comm_le
      key := fun hk2 => absurd hk2 (by omega)
      Ym_ge := hφ'.Y_ge
      Ym_le := hφ'.Y_le
      Ym_comm := hYK'
      index_le := hφ'.index_le
      Kp_le := hcentZ hKU hKc
      Kp_n := hcentn hKc
      Kp_L := hcentL hKc
      Kp_E := fun e he c hc => (Subgroup.mem_centralizer_iff.1 (hKc hc) e
        ((tImage_le φ _).trans h.le he))
      Km_n := hcentn hKc'
      Km_Z := hcentZ hKU' hKc'
      Km_le := ?_
      K_inf := ?_
      side := hside }
  · calc tImage φ K' ≤ tImage φ (tImage φ⁻¹ (Uq M T L)) := tImage_mono φ hKU'
      _ = Uq M T L := tImage_tImage_inv φ hUT
  · rw [eq_bot_iff, ← hKinf]
    rintro x ⟨hxK, hxK'⟩
    refine ⟨hxK, ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hxK'
    have htU : (t : G) ∈ Uq M T L := (apply_mem_tImage_iff φ t).1 (hKU hxK)
    refine apply_mem_tImage φ ⟨htU, h.Uq_le_Xq htU, ?_⟩
    show (t : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_iff.1 (hKc' ht) l (h.L_le hl)

end CFSG.Quasithin.MS93.S36E
end
