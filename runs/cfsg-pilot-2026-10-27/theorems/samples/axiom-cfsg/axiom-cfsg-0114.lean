public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem le_M_of_commutator_mem (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrK : r ∣ Nat.card t.Ky) {f : G} (hfM : f ∈ c.S.M) (hf : orderOf f = r)
    (hfK : ∀ k ∈ t.Ky, f * k * f⁻¹ * k⁻¹ ∈ c.L ⊓ t.d.N) {H : Subgroup G}
    (hH : CFSG.Open.IsTwoLocal H) (hKH : t.Ky ≤ H) (hfH : f ∈ H) : H ≤ c.S.M := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hcop : Nat.Coprime 6 (orderOf f) := by
    rw [hf, Nat.coprime_comm, hr.coprime_iff_not_dvd]
    intro hdvd
    have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hr' : r = 5 ∨ r = 6 := by omega
    rcases hr' with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · rw [h] at hr
      norm_num at hr
  have hnorm : ∀ i : Fin 3, ∀ x ∈ t.Lhat i, fbar t hfM * x * (fbar t hfM)⁻¹ ∈ t.Lhat i := by
    intro i x hx
    obtain ⟨aM, haM, rfl⟩ := Subgroup.mem_map.mp hx
    have haLf : (aM : G) ∈ t.d.Lf i := Subgroup.mem_subgroupOf.mp haM
    have hfa : f * (aM : G) * f⁻¹ ∈ t.d.Lf i :=
      (Subgroup.mem_normalizer_iff.mp
        (normalizes_Lf_of_coprime_six t hfM hcop i) (aM : G)).mp haLf
    have hfaM : f * (aM : G) * f⁻¹ ∈ t.M :=
      t.M.mul_mem (t.M.mul_mem hfM aM.2) (t.M.inv_mem hfM)
    refine Subgroup.mem_map.mpr ⟨⟨f * (aM : G) * f⁻¹, hfaM⟩,
      Subgroup.mem_subgroupOf.mpr hfa, ?_⟩
    change t.qmk ⟨f * (aM : G) * f⁻¹, hfaM⟩ =
      fbar t hfM * t.qmk aM * (fbar t hfM)⁻¹
    rw [fbar, ← map_mul, ← map_inv]
    rfl
  have hdelta : ∀ u : ↥(t.Lhat 0),
      fbar t hfM * t.delta u * (fbar t hfM)⁻¹ = t.delta u := by
    intro u
    have hz : t.delta u ∈ t.phiKy.range := by
      have hz' : t.delta u ∈ (t.Ky.subgroupOf t.M).map t.qmk :=
        t.delta_range_le_image_Ky ⟨u, rfl⟩
      rwa [← t.phiKy_range] at hz'
    exact fbar_commute_phiKy t hK32 hGA hSp hfM hfK hz
  have hmuL := t.muL_injective hK32 hGA hSp
  have hcent_Lhat : ∀ i : Fin 3, ∀ x ∈ t.Lhat i,
      fbar t hfM * x * (fbar t hfM)⁻¹ = x :=
    centralizes_Lhat_of_normalizes_of_centralizes_delta t hmuL hnorm hdelta
  have hcent_L : ∀ z ∈ (c.L.subgroupOf t.M).map t.qmk,
      fbar t hfM * z * (fbar t hfM)⁻¹ = z := by
    intro z hz
    rw [← t.muL_range] at hz
    obtain ⟨⟨⟨a, b⟩, e⟩, rfl⟩ := MonoidHom.mem_range.mp hz
    rw [t.muL_apply]
    have ha := hcent_Lhat 0 (a : t.Mb) a.2
    have hb := hcent_Lhat 1 (b : t.Mb) b.2
    have he := hcent_Lhat 2 (e : t.Mb) e.2
    calc fbar t hfM * ((a : t.Mb) * (b : t.Mb) * (e : t.Mb)) * (fbar t hfM)⁻¹
        = (fbar t hfM * (a : t.Mb) * (fbar t hfM)⁻¹) *
            (fbar t hfM * (b : t.Mb) * (fbar t hfM)⁻¹) *
            (fbar t hfM * (e : t.Mb) * (fbar t hfM)⁻¹) := by group
      _ = (a : t.Mb) * (b : t.Mb) * (e : t.Mb) := by rw [ha, hb, he]
  have hfM_ord : orderOf (fM t hfM) = r := by
    rw [← Subgroup.orderOf_coe (fM t hfM)]
    exact hf
  have hfM_notKq : fM t hfM ∉ t.Kq :=
    not_mem_Kq_of_orderOf_eq_prime t hr hr2 hfM_ord
  have hfbar_ne : fbar t hfM ≠ 1 := fun h1 =>
    hfM_notKq ((QuotientGroup.eq_one_iff _).mp h1)
  have hfbar_not_mem : fbar t hfM ∉ (c.L.subgroupOf t.M).map t.qmk := by
    intro hmem
    have hzC : ∀ w ∈ (c.L.subgroupOf t.M).map t.qmk,
        fbar t hfM * w = w * fbar t hfM := by
      intro w hw
      have h := hcent_L w hw
      calc fbar t hfM * w = (fbar t hfM * w * (fbar t hfM)⁻¹) * fbar t hfM := by
            group
        _ = w * fbar t hfM := by rw [h]
    have h1 : fbar t hfM = 1 :=
      eq_one_of_mem_image_L_of_centralizes t hK32 hGA hSp hmem hzC
    exact hfbar_ne h1
  have hfbar_ord : orderOf (fbar t hfM) = r := by
    have hdvd : orderOf (fbar t hfM) ∣ r := by
      have h := orderOf_map_dvd t.qmk (fM t hfM)
      rwa [hfM_ord] at h
    rcases hr.eq_one_or_self_of_dvd (orderOf (fbar t hfM)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hfbar_ne
    · exact h
  have hr_dvd_range : r ∣ Nat.card ↥t.phiKy.range := by
    have hr_not_dvd_inf : ¬ r ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
      have hN : IsPGroup 2 ↥(t.Ky ⊓ t.d.N) := by
        have hN2 : IsPGroup 2 ↥t.d.N :=
          CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.d.M
        exact hN2.to_le inf_le_right
      obtain ⟨n, hn⟩ := hN.exists_card_eq
      intro hrdvd
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hn] at hrdvd)
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    have hker_le : (t.phiKy.ker : Subgroup ↥t.Ky) ≤
        (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk
      have hq : t.qmk (⟨(k : G), t.Ky_le_M k.2⟩ : ↥t.M) = 1 := by
        change t.phiKy k = 1
        exact hk
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨k.2, ?_⟩)
      exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)).2
    have hker_dvd : Nat.card ↥(t.phiKy.ker) ∣ Nat.card ↥(t.Ky ⊓ t.d.N) := by
      have h1 := Subgroup.card_dvd_of_le hker_le
      have hcard_sub : Nat.card ↥((t.Ky ⊓ t.d.N).subgroupOf t.Ky) =
          Nat.card ↥(t.Ky ⊓ t.d.N) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : t.Ky ⊓ t.d.N ≤ t.Ky)).toEquiv
      rwa [hcard_sub] at h1
    have hnot : ¬ r ∣ Nat.card ↥(t.phiKy.ker) :=
      fun h => hr_not_dvd_inf (h.trans hker_dvd)
    have hprod : r ∣ Nat.card ↥(t.phiKy.ker) * Nat.card ↥(t.phiKy.range) := by
      rw [Subgroup.card_ker_mul_card_range]
      exact hrK
    rcases hr.dvd_mul.mp hprod with h | h
    · exact absurd h hnot
    · exact h
  have hrLhat0 : r ∣ Nat.card ↥(t.Lhat 0) := by
    have hcard : Nat.card ↥(t.Lhat 0) = Nat.card ↥(t.phiKy.range) := by
      rw [t.phiKy_range_eq_delta_range hK32 hGA hSp]
      exact Nat.card_congr (MonoidHom.ofInjective (t.delta_injective hmuL)).toEquiv
    rwa [hcard]
  have h3rank : 3 ≤ CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) :=
    three_le_pRank_image_L t hr2 hrLhat0
  obtain ⟨E3, hE3_le, hE3_abel, hE3_card⟩ :=
    CFSG.SectionRank.exists_pRank (p := r) hr.one_lt ((c.L.subgroupOf t.M).map t.qmk)
  have hfbar_not_E3 : fbar t hfM ∉ E3 := fun h => hfbar_not_mem (hE3_le h)
  have hfbar_pow : (fbar t hfM) ^ r = 1 := by
    rw [← hfbar_ord]
    exact pow_orderOf_eq_one _
  have hfbar_comm_E3 : ∀ a ∈ E3, a * fbar t hfM = fbar t hfM * a := by
    intro a ha
    have h := hcent_L a (hE3_le ha)
    have h' : fbar t hfM * a = a * fbar t hfM := by
      calc fbar t hfM * a = (fbar t hfM * a * (fbar t hfM)⁻¹) * fbar t hfM := by
            group
        _ = a * fbar t hfM := by rw [h]
    exact h'.symm
  obtain ⟨hE4_abel, hE4_card⟩ :=
    CFSG.Quasithin.H13.U3.elemAbelian_sup_zpowers (p := r) (A := E3)
      hE3_abel hfbar_not_E3 hfbar_pow hfbar_comm_E3
  have h4top : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) := by
    have hle := CFSG.SectionRank.le_pRank (p := r) hr.one_lt
      (H := (⊤ : Subgroup (t.Mb))) (E := E3 ⊔ Subgroup.zpowers (fbar t hfM))
      le_top hE4_abel (k := CFSG.Open.pRank r ((c.L.subgroupOf t.M).map t.qmk) + 1) ?_
    · omega
    · rw [hE4_card, hE3_card, pow_succ]
  have hnotdvd_Kq : ¬ r ∣ Nat.card ↥(t.Kq) := by
    obtain ⟨k, hk⟩ := t.Kq_isPGroup.exists_card_eq
    intro hrdvd
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow (by rwa [hk] at hrdvd)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
  have hEq : CFSG.Open.pRank r (⊤ : Subgroup (t.Mb)) = CFSG.Open.pRank r c.S.M := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r (t.Mb),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr (t.Kq) hnotdvd_Kq,
      CFSG.SectionRank.pRank_coe_eq_openPRank r (t.M)]
  have h4M : 4 ≤ CFSG.Open.pRank r c.S.M := hEq ▸ h4top
  have hrσ : r ∈ c.sig := c.four_le_imp_mem r hr hr2 h4M
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card' (G := ↥t.Ky) r hrK
  let X : Subgroup G := H ⊓ c.S.M
  have hX_le_M : X ≤ t.M := inf_le_right
  have hX_le_H : X ≤ H := inf_le_left
  let qX : ↥X →* t.Mb := (t.qmk).comp (Subgroup.inclusion hX_le_M)
  let fX : ↥X := ⟨f, Subgroup.mem_inf.mpr ⟨hfH, hfM⟩⟩
  have hKyM : t.Ky ≤ t.M := (t.Ky_le.trans inf_le_left).trans c.hyp81.1
  let vX : ↥X := ⟨v, Subgroup.mem_inf.mpr ⟨hKH v.2, hKyM v.2⟩⟩
  have hqg : qX fX = fbar t hfM := rfl
  have hqv : qX vX = t.qmk (kM t v) := rfl
  have hvM_ord : orderOf (kM t v) = r := by
    rw [← Subgroup.orderOf_coe (kM t v)]
    have hcoe : ((kM t v : ↥t.M) : G) = (v : G) := by simp [kM]
    rw [hcoe, Subgroup.orderOf_coe, hvord]
  have hvM_notKq : kM t v ∉ t.Kq :=
    not_mem_Kq_of_orderOf_eq_prime t hr hr2 hvM_ord
  have hvbar_ord : orderOf (t.qmk (kM t v)) = r :=
    orderOf_qmk_eq_of_not_mem_Kq t hr hr2 hvM_ord hvM_notKq
  have hvbar_mem_imageL : t.qmk (kM t v) ∈ (c.L.subgroupOf t.M).map t.qmk :=
    Subgroup.mem_map.mpr ⟨kM t v, (t.Ky_le v.2).1, rfl⟩
  have hvbar_mem_range : t.qmk (kM t v) ∈ qX.range := ⟨vX, hqv⟩
  have hfbar_mem_range : fbar t hfM ∈ qX.range := ⟨fX, hqg⟩
  have hfbar_not_zpowers : fbar t hfM ∉ Subgroup.zpowers (t.qmk (kM t v)) :=
    fun hmem => hfbar_not_mem (Subgroup.zpowers_le.mpr hvbar_mem_imageL hmem)
  have hcomm_gv : fbar t hfM * t.qmk (kM t v) = t.qmk (kM t v) * fbar t hfM := by
    have hz : t.qmk (kM t v) ∈ t.phiKy.range := by
      rw [t.phiKy_range]
      exact Subgroup.mem_map.mpr ⟨kM t v, Subgroup.mem_subgroupOf.mpr v.2, rfl⟩
    have h := fbar_commute_phiKy t hK32 hGA hSp hfM hfK hz
    calc fbar t hfM * t.qmk (kM t v) =
        (fbar t hfM * t.qmk (kM t v) * (fbar t hfM)⁻¹) * fbar t hfM := by group
      _ = t.qmk (kM t v) * fbar t hfM := by rw [h]
  have hcomm_zpowers : ∀ a ∈ Subgroup.zpowers (t.qmk (kM t v)),
      a * fbar t hfM = fbar t hfM * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (show Commute (t.qmk (kM t v)) (fbar t hfM) from hcomm_gv.symm).zpow_left n
      |>.eq
  have hEbar := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := r) (X := Subgroup.zpowers (t.qmk (kM t v))) (v := fbar t hfM)
    (by rw [Nat.card_zpowers, hvbar_ord]) hfbar_ord hfbar_not_zpowers hcomm_zpowers
  have h2range : 2 ≤ CFSG.Open.pRank r qX.range := by
    have hEbar_le : Subgroup.zpowers (t.qmk (kM t v)) ⊔
        Subgroup.zpowers (fbar t hfM) ≤ qX.range :=
      sup_le (Subgroup.zpowers_le.mpr hvbar_mem_range)
        (Subgroup.zpowers_le.mpr hfbar_mem_range)
    exact CFSG.SectionRank.le_pRank hr.one_lt hEbar_le hEbar.1 (k := 2) hEbar.2
  have hker2 : IsPGroup 2 ↥qX.ker := by
    have hcomap2 : IsPGroup 2 ↥((t.Kq).comap (Subgroup.inclusion hX_le_M)) :=
      t.Kq_isPGroup.comap_of_injective (Subgroup.inclusion hX_le_M)
        (Subgroup.inclusion_injective hX_le_M)
    refine hcomap2.to_le ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hrank_eq : CFSG.Open.pRank r (⊤ : Subgroup ↥X) =
      CFSG.Open.pRank r qX.range := by
    have hquot := CFSG.SectionRank.pRank_quotient_two_group (G := ↥X) qX.ker hker2 hr hr2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
        (QuotientGroup.quotientKerEquivRange qX)] at hquot
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top r qX.range,
      CFSG.SectionRank.pRank_coe_eq_openPRank r qX.range] at hquot
    exact hquot.symm
  have h2X : 2 ≤ CFSG.Open.pRank r X := by
    have hXeq : CFSG.Open.pRank r X = CFSG.Open.pRank r (⊤ : Subgroup ↥X) := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank r X,
        CFSG.SectionRank.pRank_eq_open_pRank_top r ↥X]
    rw [hXeq, hrank_eq]
    exact h2range
  exact c.u2 r hrσ H hH h2X

end CaseTwoTransitive
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
end
