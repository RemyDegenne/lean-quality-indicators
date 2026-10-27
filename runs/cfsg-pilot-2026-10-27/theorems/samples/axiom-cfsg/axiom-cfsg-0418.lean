public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Comm

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem neg_single_mem_roots (i : Fin D.rank) : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (single_mem_roots i)

end Comm
end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
end
