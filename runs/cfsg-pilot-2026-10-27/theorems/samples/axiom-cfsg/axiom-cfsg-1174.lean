public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

namespace HypE27

open TorusE27 SpE27

variable {K : Type} [Field K]

variable [CharP K 2]

theorem T0_map {ω : K} (σ : K ≃+* K) (hσ : σ ω = ω) (v : Fin 3 → ZMod 3) :
    (T0 ω v).map σ = T0 ω v := by
  have hc : ∀ x, σ (chi ω x) = chi ω x := fun x => by rw [chi, map_pow, hσ]
  simp [T0, fromBlocks_map, diagonal_map, hc]

end HypE27
end CFSG.LocalAnalysis.RankThreeTheoremC
end
