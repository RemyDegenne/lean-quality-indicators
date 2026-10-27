public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Theorem

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
  {A' X₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2AlmostSimple.l34BlockFacts
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar A' X₀ K)
    (hcard : Nat.card K = 20160)
    (hNH : H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) :=
  l34BlockFacts_of_unique hK.unique hK.center_eq_bot hcard hNH hLw hLW

end Theorem
end CFSG.AGLEmbeddingD2
end
