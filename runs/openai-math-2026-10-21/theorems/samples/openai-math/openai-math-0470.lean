namespace OAI

noncomputable section

open Classical Set Metric Topology

open Set Topology

open scoped unitInterval

namespace EilenbergGanea.CoverTopology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

variable (p : E → X)

variable {p} (cov : IsCoveringMap p)

include cov

theorem isQuotientCoveringMap_deck [ContractibleSpace E] (hs : Function.Surjective p) :
    IsQuotientCoveringMap p (deckGroup p) where
  __ := cov.isQuotientMap hs
  __ := deckContinuous p
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      obtain ⟨d,hd,_⟩ := existsUnique_deck cov y x h.symm
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact deck_project p d y
  disjoint := by
    intro x
    obtain ⟨U,hU,hxU,hinj⟩ := cov.isLocalHomeomorph.isLocallyInjective x
    refine ⟨U,hU.mem_nhds hxU,?_⟩
    rintro d ⟨z,⟨y,hyU,rfl⟩,hzU⟩
    apply deck_ext cov y
    exact hinj hzU hyU (deck_project p d y)

end EilenbergGanea.CoverTopology
end
end OAI
