public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem commutator_ppQuot_of_component {p : ℕ} [Fact p.Prime] {X J : Subgroup G} (hJX : J ≤ X)
    (h : GLAPComponent p X J) : commutator (ppQuot p ↥J) = ⊤ := by
  unfold GLAPComponent at h
  obtain ⟨-, -, hcomp, -⟩ := h
  obtain ⟨-, -, hq⟩ := hcomp
  set PX : Subgroup ↥X := GLAPPrimeCore p ↥X with hPX
  set H : Subgroup (↥X ⧸ PX) := (J.subgroupOf X).map (QuotientGroup.mk' PX) with hH
  have hHperf : commutator ↥H = ⊤ := hq.1
  have hmem : ∀ x : ↥J, (QuotientGroup.mk' PX) (Subgroup.inclusion hJX x) ∈ H := by
    intro x
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
  let g : ↥J →* ↥H :=
    MonoidHom.codRestrict ((QuotientGroup.mk' PX).comp (Subgroup.inclusion hJX)) H hmem
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 y.2
    refine ⟨⟨z.1, Subgroup.mem_subgroupOf.1 hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  have hker : g.ker ≤ GLAPPrimeCore p ↥J := by
    set K0 : Subgroup ↥J := PX.comap (Subgroup.inclusion hJX) with hK0
    have hK0le : g.ker ≤ K0 := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : (QuotientGroup.mk' PX) (Subgroup.inclusion hJX x) = 1 := by
        have := congrArg Subtype.val hx
        simpa [g] using this
      rw [hK0, Subgroup.mem_comap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at *
      exact h1
    have hK0normal : K0.Normal := by
      rw [hK0]
      exact Subgroup.Normal.comap (inferInstance : PX.Normal) _
    have hK0cop : Nat.Coprime p (Nat.card K0) := by
      have hinj : Function.Injective (Subgroup.inclusion hJX) := Subgroup.inclusion_injective hJX
      have hmapcard : Nat.card (K0.map (Subgroup.inclusion hJX)) = Nat.card K0 :=
        Subgroup.card_map_of_injective hinj
      have hle : K0.map (Subgroup.inclusion hJX) ≤ PX := by
        rw [hK0]
        exact Subgroup.map_comap_le _ _
      have hdvd : Nat.card K0 ∣ Nat.card PX := by
        rw [← hmapcard]
        exact Subgroup.card_dvd_of_le hle
      exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
    have hmemS : K0 ∈ {K : Subgroup ↥J | K.Normal ∧ Nat.Coprime p (Nat.card K)} :=
      ⟨hK0normal, hK0cop⟩
    exact fun x hx => le_sSup hmemS (hK0le hx)
  have hmapJ : Subgroup.map g (commutator ↥J) = ⊤ := by
    have h1 : Subgroup.map g (commutator ↥J) = commutator ↥H := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective g hgsurj]
    rw [h1, hHperf]
  have hcov : commutator ↥J ⊔ g.ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : g x ∈ Subgroup.map g (commutator ↥J) := by
      rw [hmapJ]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 hx
    have hk : c⁻¹ * x ∈ g.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have : x = c * (c⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hc hk
  have hcovO : commutator ↥J ⊔ GLAPPrimeCore p ↥J = ⊤ := by
    rw [eq_top_iff, ← hcov]
    exact sup_le_sup_left hker _
  have hquot : Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (commutator ↥J) = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
        (commutator ↥J ⊔ GLAPPrimeCore p ↥J) = ⊤ := by
      rw [hcovO]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Subgroup.map_sup] at h1
    have h2 : Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (GLAPPrimeCore p ↥J) = ⊥ := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff y).2 hy
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact Subgroup.one_mem _
    rw [h2, sup_bot_eq] at h1
    exact h1
  have hc : Subgroup.map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (commutator ↥J) =
      commutator (ppQuot p ↥J) := by
    show Subgroup.map _ ⁅(⊤ : Subgroup ↥J), ⊤⁆ = ⁅(⊤ : Subgroup (ppQuot p ↥J)), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [← hc, hquot]

end Perfect
end CFSG.LocalAnalysis.GLTheoremA.I2015
end
