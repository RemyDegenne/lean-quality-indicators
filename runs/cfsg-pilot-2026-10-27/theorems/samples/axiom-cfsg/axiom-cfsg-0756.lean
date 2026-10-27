public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

open CFSG.AGLEmbedding (CatalogSimpleSections catalogSimpleSections_of_isKProper)

variable {G : Type} [Group G] [Finite G]

theorem rankThreeLocalRank_lt_three_of_three_mem_sigmaA (hrank : evenRank G = 3)
    (h3 : 3 ∈ rankThreeSigmaA G) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    rankThreeLocalRank q G < 3 := by
  classical
  by_contra hlt
  push Not at hlt
  have hupper := rankThreeLocalRank_le_evenRank (G := G) q hq (by omega)
  have hupper3 := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  have hq_eq : rankThreeLocalRank q G = 3 := by omega
  obtain ⟨H, -, hHrank⟩ := rankThreeLocalRank_attained (G := G) q (by omega)
  have hqdvd : q ∣ Nat.card G := prime_dvd_card_of_pRank_pos q H (by omega)
  have hS3 : ({p : ℕ | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}).Nonempty :=
    ⟨q, hq, hq3, hqdvd, hq_eq⟩
  dsimp only [rankThreeSigmaA] at h3
  split_ifs at h3
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC
end
