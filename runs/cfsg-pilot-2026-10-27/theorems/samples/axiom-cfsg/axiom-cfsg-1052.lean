public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Roots

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

theorem reflection_mem_roots {i : Fin D.rank} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    reflection D.cartan i γ ∈ D.roots := by
  have := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) hγ
  rwa [weylAction_simple] at this

end Roots
end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
end
