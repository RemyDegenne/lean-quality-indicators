public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem P2251m.exists_elemAbelian_of_pair_of_not_dvd {M K L : Subgroup G} (hK : K ∈ calC M)
    (hKn : (K.subgroupOf M).Normal) (hL : L ∈ calC M) (hKL : K ≠ L) (hKs : BadShape22 (Bar2 K))
    (hLs : LayerShape22 (Bar2 L)) (hM3 : CFSG.Open.pRank 3 M ≤ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 3 ≤ CFSG.Open.pRank p M) (hpK : ¬ p ∣ Nat.card (Bar2 K)) :
    ∃ R E A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ A ≤ M ⊓ centralizer (E : Set G) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hMK : M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hK.1.le).1 hKn
  have hK3 := hKs.layerShape.three_dvd_card
  have hKZ := hKs.layerShape.center_eq_bot
  have hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G) := fun _ hHM hH =>
    P2251c.le_normalizer_of_pRank_le hK hKn hL hKL hK3 hKZ hLs.three_dvd_card hLs.center_eq_bot hM3 hHM hH
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hM
  have hA₀K := hA₀M.trans hMK
  have hA₀L := hLN A₀ hA₀M (hA₀c ▸ (hp.odd_of_ne_two hp2).pow)
  have hexp : ∀ w : ↥A₀, w ^ p = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA₀.2 _ w.2)
  have hpA := hKs.not_dvd_card_mulAut_of_not_dvd hp hp5 hpK
  have hA₀C : ∀ w : ↥A₀, UC6S846.rhoL K (inclusion hA₀K w) = 1 := fun w => by
    have h1 : (UC6S846.rhoL K (inclusion hA₀K w)) ^ p = 1 := by rw [← map_pow, ← map_pow, hexp, map_one, map_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard _) hpA
  obtain ⟨Q, hQA₀, hQc, b, hbL, hb3, hbQ⟩ : ∃ Q ≤ A₀, p ^ 2 ≤ Nat.card Q ∧ ∃ b ∈ L, orderOf b = 3 ∧
      ∀ u ∈ Q, b⁻¹ * (u * b * u⁻¹) ∈ pCoreOf 2 L := by
    obtain ⟨x, hx3, Q, hQc, hQx⟩ := P2251d.exists_orderOf_three_card_le_of_layerShape hLs hp hp2 hexp
      (fun x y => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hA₀.comm x.2 y.2))
      ((UC6S846.rhoL L).comp (inclusion hA₀L)) hA₀c.ge
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have h3l : 3 ∣ orderOf l := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l
      rwa [QuotientGroup.mk'_apply, hx3] at h
    have hfix : ∀ v ∈ Q, UC6S846.rhoL L (inclusion hA₀L v) ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) =
        ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) := fun v hv => by
      rw [QuotientGroup.mk_pow, map_pow]
      exact congrArg (· ^ (orderOf l / 3)) (hQx v hv)
    refine ⟨Q.map A₀.subtype, map_subtype_le _, by rwa [card_map_of_injective A₀.subtype_injective], _,
      (l ^ (orderOf l / 3)).2, by rw [Subgroup.orderOf_coe]; exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hA₀L v) (l ^ (orderOf l / 3)).2 (hfix v hv)
  obtain ⟨b₁, hb₁K, hb₁⟩ := P2251c.exists_orderOf_three_mem hK3
  refine R8107Pair.exists_elemAbelian_of_fixed_pair hK hL hKL (fun _ hHM _ => hHM.trans hMK) hLN hKZ
    (fun _ hBK hB => uc22p2251b_isCyclic_of_isPGroup hKs.layerShape Nat.prime_three (by norm_num) hBK hB)
    (fun _ hBL hB => uc22p2251b_isCyclic_of_isPGroup hLs Nat.prime_three (by norm_num) hBL hB)
    hp hp2 (hQA₀.trans hA₀M) (hA₀.mono hQA₀) hQc hb₁K hb₁ (fun u hu => ?_) hbL hb3 hbQ
  exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hA₀K ⟨u, hQA₀ hu⟩) hb₁K
    (by rw [hA₀C ⟨u, hQA₀ hu⟩, MulAut.one_apply])

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
