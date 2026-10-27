public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

open CFSG.LocalAnalysis.WeakClosure81.SevenK

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem commute_of_commuting_images (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U W : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hW : W ∈ omegaSet V H E) {d e : ↥(kSub V H E)}
    (hd : (d : G) ∈ U) (he : (e : G) ∈ W) (hd1 : (d : G) ∉ pCoreOf 2 H)
    (he1 : (e : G) ∉ pCoreOf 2 H) (hcomm : φ d * φ e = φ e * φ d) :
    ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hd2, -, hdUbar⟩ := triaAmb_bar_eq_zpowers h hφ hS hU hd hd1
  obtain ⟨-, he2, -, heWbar⟩ := triaAmb_bar_eq_zpowers h hφ hS hW he he1
  have hcommC : Commute (φ d) (φ e) := hcomm
  obtain ⟨a, b, hUa, hWb, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hU hW
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)
  have hUW : U ⊔ W ≤ kSub V H E := sup_le (le_kSub hU) (le_kSub hW)
  have hP : IsPGroup 2 ↥(U ⊔ W) := by
    let T : Subgroup G := U ⊔ W ⊔ pCoreOf 2 (kSub V H E)
    let T' : Subgroup ↥(kSub V H E) := T.subgroupOf (kSub V H E)
    have hTK : T ≤ kSub V H E := sup_le hUW hJK
    have hT'map : T'.map φ = Subgroup.zpowers (φ d) ⊔ Subgroup.zpowers (φ e) := by
      change barSub (kSub V H E) φ (U ⊔ W ⊔ pCoreOf 2 (kSub V H E)) = _
      rw [barSub_sup (A := U ⊔ W) (B := pCoreOf 2 (kSub V H E)) hUW hJK φ,
        barSub_sup (A := U) (B := W) (le_kSub hU) (le_kSub hW) φ,
        hdUbar, heWbar, triaAmb_barSub_pCoreOf_eq_bot hφ]
      simp
    have hPmap : IsPGroup 2 (T'.map φ) := by
      rw [hT'map]
      refine IsPGroup.to_sup_of_normal_right' ?_ ?_ ?_
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers]
        simpa using orderOf_dvd_of_pow_eq_one hd2
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers]
        simpa using orderOf_dvd_of_pow_eq_one he2
      · refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hcommC.zpow_right n).symm
    have hker_eq : φ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hφ.ker_iff k
    have hJ2 : IsPGroup 2 (pCoreOf 2 (kSub V H E)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)
    have hker2 : IsPGroup 2 φ.ker := by
      rw [hker_eq]
      exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJK).symm
    have hker_le : φ.ker ≤ T' := by
      intro k hk
      rw [hker_eq] at hk
      change (k : G) ∈ U ⊔ W ⊔ pCoreOf 2 (kSub V H E)
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk)
    have hT'2 : IsPGroup 2 T' := by
      have hh := hPmap.comap_of_ker_isPGroup φ hker2
      rwa [Subgroup.comap_map_eq_self hker_le] at hh
    have hT2 : IsPGroup 2 T := hT'2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK)
    exact hT2.to_le le_sup_left
  have hN' : U ⊓ Subgroup.normalizer (W : Set G) ≠ ⊥ := by
    rw [hUa, hWb]
    exact hN
  intro u hu w hw
  exact commute_of_isPGroup_sup h.elemAbelian h.ti ⟨a, hUa⟩ ⟨b, hWb⟩ hN' hP u hu w hw

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
end
