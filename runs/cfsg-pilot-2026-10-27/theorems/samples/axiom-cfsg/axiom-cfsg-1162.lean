public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156Res4

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree Subgroup Equiv

open CFSG.RankThree.Native.ONTriple

variable {X : Type} [Group X]

section Model

theorem exists_centralizer_eq
    (ψ : X ≃* GM) {b : X}
    (hb3 : b ^ 3 = 1) (hbz : b ∉ center X) :
    ∃ K : Subgroup X, centralizer ({b} : Set X) = zpowers b ⊔ K ∧ zpowers b ⊓ K = ⊥ ∧
      center X ≤ K ∧ ∃ ρ : ↥K →* Perm (Fin 6), ρ.range = alternatingGroup (Fin 6) ∧
        ∀ k : ↥K, ρ k = 1 ↔ (k : X) ∈ center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := ψ b with ha
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hb3, map_one]
  have haz : a ∉ zpowers zG := fun h => hbz ((Sec13.ON134.mem_center_iff_model ψ).2 h)
  have ha1 : a ≠ 1 := fun h => haz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ha3 ha1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have haP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers a))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 haP (conj_not_mem_zpowers haz g)
  set n := g⁻¹ * wordN w with hn
  have han : a = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← han] at h1 h2
  set KM := K0G.map (MulAut.conj n).toMonoidHom with hKM
  set K := KM.map ψ.symm.toMonoidHom with hK
  have hmapK : K.map ψ.toMonoidHom = KM := by
    rw [hK, Subgroup.map_map]
    convert Subgroup.map_id KM
    ext y
    simp
  have hinj := Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  have hzKM : zG ∈ KM := ⟨zG, zG_mem_K0', by rw [conj_zG]⟩
  have hmem : ∀ k : ↥K, n⁻¹ * ψ k * n ∈ K0G := by
    intro k
    have hk : ψ k ∈ KM := by
      rw [← hmapK]
      exact mem_map_of_mem _ k.2
    obtain ⟨m, hm, hme⟩ := hk
    have e : n⁻¹ * ψ k * n = m := by
      rw [← hme]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hm
  let ι : ↥K →* ↥K0G :=
    { toFun := fun k => ⟨n⁻¹ * ψ k * n, hmem k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k l => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]
        group) }
  have hιs : Function.Surjective ι := by
    intro y
    have hy : ψ.symm (n * y * n⁻¹) ∈ K := ⟨n * y * n⁻¹, ⟨y, y.2, rfl⟩, rfl⟩
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    show n⁻¹ * ψ (ψ.symm (n * y * n⁻¹)) * n = y
    rw [MulEquiv.apply_symm_apply]
    group
  refine ⟨K, ?_, ?_, ?_, actK.comp ι, ?_, ?_⟩
  · apply hinj
    rw [map_centralizer_singleton_equiv, h1, Subgroup.map_sup, MonoidHom.map_zpowers, hmapK]
    rfl
  · apply hinj
    rw [Subgroup.map_inf_eq _ _ _ ψ.injective, MonoidHom.map_zpowers, hmapK, Subgroup.map_bot]
    exact h2
  · intro z hz
    have hz' : ψ z ∈ zpowers zG := (Sec13.ON134.mem_center_iff_model ψ).1 hz
    have hzK : ψ z ∈ KM := zpowers_le.mpr hzKM hz'
    rw [← hmapK] at hzK
    obtain ⟨k, hk, hke⟩ := hzK
    rwa [← ψ.injective hke]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hιs, ← MonoidHom.range_eq_map,
      range_actK]
  · intro k
    have hcz : ∀ j : ℤ, n⁻¹ * zG ^ j * n = zG ^ j := fun j => by
      rw [mul_assoc, (Commute.zpow_left (zG_central n) j).eq, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have hcz' : ∀ j : ℤ, n * zG ^ j * n⁻¹ = zG ^ j := fun j => by
      rw [(Commute.zpow_left (zG_central n) j).eq.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_actK, Sec13.ON134.mem_center_iff_model ψ]
    constructor
    · intro hk
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk
      have hj' : zG ^ j = n⁻¹ * ψ k * n := congrArg Subtype.val hj
      refine mem_zpowers_iff.mpr ⟨j, ?_⟩
      have e : ψ k = n * (n⁻¹ * ψ k * n) * n⁻¹ := by group
      rw [e, ← hj', hcz']
    · intro hk
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk
      refine mem_zpowers_iff.mpr ⟨j, Subtype.ext ?_⟩
      show zG ^ j = n⁻¹ * ψ k * n
      rw [← hj, hcz]

end Model
end CFSG.RankThree.PartTwo.Sec15.Proof156Res4
end
