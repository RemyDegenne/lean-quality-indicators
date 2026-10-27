public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s218_exists_lift_centralizer {L M : Subgroup G} (hML : M ≤ normalizer (L : Set G))
    (K : Subgroup ↥L) [K.Characteristic] {p : ℕ} [Fact p.Prime] (hpK : ¬ p ∣ Nat.card K)
    {x : G} (hx : x ∈ M) (hxo : orderOf x = p) (hρ : uc22s218_rhoK L K ⟨x, hML hx⟩ = 1)
    (P : Subgroup (↥L ⧸ K)) (hcop : Nat.Coprime (Nat.card P) (Nat.card K)) :
    ∃ β : P →* ↥L, (∀ a, ∀ x' ∈ zpowers x, x' * (β a : G) = (β a : G) * x') ∧
      ∀ a, QuotientGroup.mk' K (β a) = a := by
  have hXp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hNL : K.map L.subtype ≤ L := Subgroup.map_subtype_le K
  have hpN : ¬ p ∣ Nat.card (K.map L.subtype) := by
    rwa [Subgroup.card_map_of_injective L.subtype_injective]
  have hXN : zpowers x ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 (hML hx)).trans (uc22s218_normalizer_le_normalizer_map_subtype L K)
  have hXL : ∀ x' ∈ zpowers x, ∀ l ∈ L, x' * l * x'⁻¹ * l⁻¹ ∈ K.map L.subtype := by
    intro x' hx' l hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
    exact uc22s218_conj_mul_inv_mem_of_rhoK_eq_one K
      (uc22s218_rhoK_zpow_eq_one K hML hx hρ j) ⟨l, hl⟩
  let Cx : Subgroup ↥L := (centralizer ((zpowers x : Subgroup G) : Set G)).subgroupOf L
  have hC : ∀ l : ↥L, ∃ c ∈ Cx, c⁻¹ * l ∈ K := by
    intro l
    obtain ⟨c, hc, hcl⟩ := uc22s218_exists_mem_centralizer_of_comm_mod hpN hXp hXN
      (uc22s218_le_normalizer_map_subtype L K) hNL hXL l.2
    rw [mem_inf] at hc
    refine ⟨⟨c, hc.1⟩, hc.2, ?_⟩
    have h : ((⟨c, hc.1⟩⁻¹ * l : ↥L) : G) ∈ K.map L.subtype := by simpa using hcl
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h
  obtain ⟨β, hβC, hβ⟩ := uc22s218_exists_lift_hom_of_coprime K Cx hC P hcop
  exact ⟨β, fun a x' hx' => (mem_centralizer_iff.1 (hβC a)) x' hx', hβ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
