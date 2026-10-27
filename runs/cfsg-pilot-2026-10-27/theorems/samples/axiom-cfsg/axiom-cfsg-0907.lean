public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

open CFSG.RankThree.PartOne.KCOrthogonal

open CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.AGLEmbedding.ToralCensus (PerfectThreeIn)

theorem exists_twistedD_four_of_gf2OmMinus8 (d : ValidLieTypeIndex) (h : gf2OmMinus8 d.1) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid),
      d.1 = .twistedD 4 q ∧ q.card = 2 := by
  obtain ⟨e, hv⟩ := d
  cases e with
  | twistedD r q =>
    by_cases hr : r = 4
    · subst hr
      exact ⟨q, hv, rfl, by simpa [gf2OmMinus8] using h⟩
    · exfalso
      simp [gf2OmMinus8, hr] at h
  | A r q => simp [gf2OmMinus8] at h
  | twistedA r q => simp [gf2OmMinus8] at h
  | B r q => simp [gf2OmMinus8] at h
  | C r q => simp [gf2OmMinus8] at h
  | D r q => simp [gf2OmMinus8] at h
  | E6 q => simp [gf2OmMinus8] at h
  | E7 q => simp [gf2OmMinus8] at h
  | E8 q => simp [gf2OmMinus8] at h
  | F4 q => simp [gf2OmMinus8] at h
  | G2 q => simp [gf2OmMinus8] at h
  | twistedE6 q => simp [gf2OmMinus8] at h
  | trialityD4 q => simp [gf2OmMinus8] at h
  | suzuki m => simp [gf2OmMinus8] at h
  | reeG2 m => simp [gf2OmMinus8] at h
  | reeF4 m => simp [gf2OmMinus8] at h
  | tits => simp [gf2OmMinus8] at h

end CFSG.LocalAnalysis.GLTheoremA.S262
end
