public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.Blueprint (LieModel)

section Iso

theorem isoLie_of_lieModel {X : Type} [Group X] (h : LieModel X .Tits 0 2 1) : IsoLie X .tits := by
  have hv : TauCeti.LieTypeIndex.tits.Valid := by simp
  refine ⟨hv, ?_⟩
  obtain ⟨e₁⟩ := titsModelEquiv X 2 1 (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  have hT : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₂⟩ := titsModelEquiv _ 2 1 hT
  exact ⟨e₁.trans e₂.symm⟩

end Iso
end CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut
end
