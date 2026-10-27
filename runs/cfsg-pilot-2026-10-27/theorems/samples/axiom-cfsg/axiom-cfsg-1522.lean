public section

namespace CFSG.Walter.W67.Sec65

open Sec6 BenderSuzuki.External BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {e u ρ : G} (h : Hyp65 G e u ρ)

include h

theorem false_of_card_Pstar_gt {X : Subgroup G} (hPX : PP e u ≤ X) (hX7 : IsPGroup 7 X)
    (hXc : Nat.card X = 7 ^ (Nat.card G).factorization 7)
    (hρX : ρ ∈ Subgroup.normalizer (X : Set G)) (hgt : 7 ^ 3 < Nat.card X) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set NX := Subgroup.normalizer (X : Set G) with hNX
  set x₀ : X := ⟨e, hPX e_mem_P⟩ with hx₀
  set MQ := Subgroup.centralizer ((Subgroup.upperCentralSeries X 2 : Subgroup X) : Set X)
    with hMQ
  obtain ⟨hidxQ, hx₀M⟩ := index_centralizer_upperCentralSeries_two hX7 x₀
    (h.card_centralizer_mk_e hX7 hPX) hgt
  set M := MQ.map X.subtype with hMdef
  have hMX : M ≤ X := Subgroup.map_subtype_le _
  have hMsub : M.subgroupOf X = MQ :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective MQ
  have hidx : M.relIndex X = 7 := by rw [Subgroup.relIndex, hMsub, hidxQ]
  have heM : e ∉ M := by
    rintro ⟨y, hy, hye⟩
    apply hx₀M
    have : y = x₀ := Subtype.ext hye
    rwa [← this]
  have hNM : NX ≤ Subgroup.normalizer (M : Set G) := by
    intro n hn
    apply Sec53.mem_normalizer_of_conj_le
    rintro _ ⟨y, hy, rfl⟩
    have hchar : MQ.Characteristic := inferInstance
    have hmem : conjAut hn y ∈ MQ := by
      rw [← hchar.fixed (conjAut hn).symm, Subgroup.mem_comap]
      simpa using hy
    exact ⟨conjAut hn y, hmem, rfl⟩
  have hXM : X ≤ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer.trans hNM
  have hρM : ρ ∈ Subgroup.normalizer (M : Set G) := hNM hρX
  have hME : M ⊓ Subgroup.zpowers e = ⊥ := by
    have hdvd : Nat.card ↥(M ⊓ Subgroup.zpowers e) ∣ 7 :=
      h.card_E ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h7
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : M ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h7, h.card_E])
      have : e ∈ M ⊓ Subgroup.zpowers e := by rw [heq]; exact Subgroup.mem_zpowers e
      exact heM (Subgroup.mem_inf.mp this).1
  have hEM : Subgroup.zpowers e ≤ Subgroup.normalizer (M : Set G) :=
    (E_le_P.trans hPX).trans hXM
  have hXME : M ⊔ Subgroup.zpowers e = X := by
    have hle : M ⊔ Subgroup.zpowers e ≤ X := sup_le hMX (E_le_P.trans hPX)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_sup_of_inf_eq_bot hEM hME, h.card_E]
    have h1 := Subgroup.relIndex_mul_card (H := M) (K := X)
    rw [inf_of_le_left hMX, hidx] at h1
    rw [← h1, mul_comm]
  have hcomm : ∀ g ∈ Subgroup.normalizer (M : Set G), g * e = e * g →
      ∀ y ∈ X, g * y * g⁻¹ * y⁻¹ ∈ M := by
    intro g hgM hge y hy
    rw [← hXME] at hy
    obtain ⟨m, hm, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hEM).mp hy
    have hga : g * a = a * g := comm_of_mem_zpowers hge ha
    have hgm : g * m * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hgM m).mp hm
    have hag : a * g⁻¹ = g⁻¹ * a := by
      calc a * g⁻¹ = g⁻¹ * (g * a) * g⁻¹ := by group
        _ = g⁻¹ * (a * g) * g⁻¹ := by rw [hga]
        _ = g⁻¹ * a := by group
    have e1 : g * (m * a) * g⁻¹ * (m * a)⁻¹ = (g * m * g⁻¹) * m⁻¹ := by
      calc g * (m * a) * g⁻¹ * (m * a)⁻¹ = g * m * (a * g⁻¹) * a⁻¹ * m⁻¹ := by group
        _ = g * m * (g⁻¹ * a) * a⁻¹ * m⁻¹ := by rw [hag]
        _ = (g * m * g⁻¹) * m⁻¹ := by group
    rw [e1]
    exact M.mul_mem hgm (M.inv_mem hm)
  have hfpf : M ⊓ Subgroup.centralizer ({ρ} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hME]
    refine le_inf inf_le_left ?_
    rw [← h.inf_centralizer_ρ_of_le hX7 hPX]
    exact inf_le_inf_right _ hMX
  have hMlcs := lowerCentralSeries_two_eq_bot_of_fpf hρM h.ρ_pow_three hfpf
  have hodd : Odd (Nat.card NX) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨⟨t, htN⟩, hto⟩ := exists_prime_orderOf_dvd_card' (G := NX) 2 h2
    rw [Subgroup.orderOf_mk] at hto
    have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
    have := h.eq_one_of_mem_normalizer hX7 hPX htN ht2
    rw [this, orderOf_one] at hto
    norm_num at hto
  have hR : Subgroup.zpowers ρ ≤ NX := Subgroup.zpowers_le.mpr hρX
  have hRc : Nat.card (Subgroup.zpowers ρ) = 3 ^ (Nat.card NX).factorization 3 := by
    have h3le : (Nat.card NX).factorization 3 ≤ 1 :=
      h.factorization_three_le hρX (h.inf_centralizer_ρ_of_le hX7 hPX)
    have h3ge : 1 ≤ (Nat.card NX).factorization 3 := by
      have hd : 3 ∣ Nat.card NX := by
        have := Subgroup.card_dvd_of_le hR
        rwa [Nat.card_zpowers, h.orderOf_ρ] at this
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp hd
    rw [Nat.card_zpowers, h.orderOf_ρ, show (Nat.card NX).factorization 3 = 1 by omega, pow_one]
  have h3 : ∀ t ∈ NX, (∃ k : ℕ, t ^ 3 ^ k = 1) → ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ M := by
    rintro t htN ⟨k, hk⟩ x hx
    obtain ⟨c, hcN, hc⟩ := exists_le_cj_of_sylowIn hR hRc (Subgroup.zpowers_le.mpr htN)
      (Huppert.isPGroup_zpowers hk)
    have htc : c⁻¹ * t * c ∈ Subgroup.zpowers ρ := mem_cj.mp (hc (Subgroup.mem_zpowers t))
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp htc
    have hy : c⁻¹ * x * c ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (NX.inv_mem hcN) x).mp hx
      simpa using this
    have hρi : ρ ^ i ∈ Subgroup.normalizer (M : Set G) := Subgroup.zpow_mem _ hρM i
    have hρie : ρ ^ i * e = e * ρ ^ i := (Commute.zpow_left (h.comm_eρ.symm : Commute ρ e) i).eq
    have h1 := hcomm _ hρi hρie _ hy
    have e1 : t * x * t⁻¹ * x⁻¹ =
        c * (ρ ^ i * (c⁻¹ * x * c) * (ρ ^ i)⁻¹ * (c⁻¹ * x * c)⁻¹) * c⁻¹ := by
      rw [hi]
      group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (hNM hcN) _).mp h1
  have htriv := conj_mem_of_relIndex_eq_seven hMX hXM le_rfl hNM hidx hodd h3
  have hMX' : M ≠ X := fun hMXeq => heM (hMXeq ▸ hPX e_mem_P)
  set Psyl : Sylow 7 G := Sylow.ofCard X hXc with hPsyl
  have hPsylX : (Psyl : Subgroup G) = X := Sylow.coe_ofCard _ _
  by_cases hw : WeaklyClosedIn X M
  ·
    have hHW := hallPResidual_normalizer_eq_top h.perfect Psyl (by rw [hPsylX]; exact hw)
      (Or.inl (engelSymbol_eq_one_of_lowerCentralSeries hMlcs (by norm_num)))
    exact hallPResidual_ne_top_of_quot hXM hMX le_rfl hX7
      (card_eq_of_le_of_card_eq hXM hXc) hMX' (fun n _ hn x hx => htriv n hn x hx) hHW
  ·
    have hw' : ∃ g : G, rightConjugate M g ≤ X ∧ rightConjugate M g ≠ M := by
      by_contra hno
      push Not at hno
      exact hw ⟨hMX, hno⟩
    obtain ⟨g, hgX, hgM⟩ := hw'
    set M' := rightConjugate M g with hM'
    have hM'cj : M' = cj g⁻¹ M := rfl
    have hM'c : Nat.card M' = Nat.card M := by rw [hM'cj, card_cj]
    have hidx' : M'.relIndex X = 7 := by
      apply relIndex_eq_of_card hgX
      have h1 := Subgroup.relIndex_mul_card (H := M) (K := X)
      rw [inf_of_le_left hMX, hidx] at h1
      rw [hM'c, ← h1, mul_comm]
    have hXM' : X ≤ Subgroup.normalizer (M' : Set G) := by
      have hXmin : (Nat.card X).minFac = 7 := by
        obtain ⟨k, hk⟩ := hX7.exists_card_eq
        rw [hk]
        refine Nat.Prime.pow_minFac (by norm_num) ?_
        rintro rfl
        rw [hk, pow_zero] at hgt
        norm_num at hgt
      have hn : (M'.subgroupOf X).Normal :=
        Subgroup.normal_of_index_eq_minFac_card (by rw [hXmin]; exact hidx')
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hgX).mp hn
    have hsup : M ⊔ M' = X := by
      have hle : M ⊔ M' ≤ X := sup_le hMX hgX
      have hlt : Nat.card M < Nat.card ↥(M ⊔ M') := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) fun heq => hgM ?_
        have hMeq : M ⊔ M' = M := (Subgroup.eq_of_le_of_card_ge le_sup_left heq.symm.le).symm
        exact Subgroup.eq_of_le_of_card_ge (hMeq ▸ le_sup_right) hM'c.symm.le
      have hdvd : Nat.card ↥(M ⊔ M') ∣ Nat.card X := Subgroup.card_dvd_of_le hle
      have hMdvd : Nat.card M ∣ Nat.card ↥(M ⊔ M') := Subgroup.card_dvd_of_le le_sup_left
      have h1 := Subgroup.relIndex_mul_card (H := M) (K := X)
      rw [inf_of_le_left hMX, hidx] at h1
      obtain ⟨k, hk⟩ := hMdvd
      have hk7 : k ∣ 7 := by
        rw [← h1, hk, mul_comm 7] at hdvd
        exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd
      rcases (Nat.dvd_prime (by norm_num)).mp hk7 with hk1 | hk1
      · rw [hk, hk1, mul_one] at hlt
        exact absurd hlt (lt_irrefl _)
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hk1, ← h1, mul_comm])
    have hM'lcs : M'.lowerCentralSeries 2 = ⊥ := by
      rw [hM'cj, ← Subgroup.map_lowerCentralSeries, hMlcs, Subgroup.map_bot]
    have hXlcs : X.lowerCentralSeries 4 = ⊥ := by
      rw [← hsup]
      exact fitting_lowerCentralSeries_sup_eq_bot M M' (hsup ▸ hXM) (hsup ▸ hXM') hMlcs hM'lcs
    have hHW := hallPResidual_normalizer_eq_top h.perfect Psyl (weaklyClosedIn_self Psyl)
      (Or.inl (by
        rw [hPsylX]
        exact engelSymbol_eq_one_of_lowerCentralSeries hXlcs (by norm_num)))
    rw [hPsylX] at hHW
    exact hallPResidual_ne_top_of_quot Subgroup.le_normalizer hMX hNM hX7
      (card_eq_of_le_of_card_eq Subgroup.le_normalizer hXc) hMX'
      (fun n hn _ x hx => htriv n hn x hx) hHW

end Hyp65
end CFSG.Walter.W67.Sec65
end
