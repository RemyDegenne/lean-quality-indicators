public noncomputable section

namespace ConwayRefinement.Standalone.InlineConwayRefinement

universe u

theorem Game.toSupport_fromSupport (x : SupportGame.{u}) :
    Game.toSupport (Game.fromSupport x) = x := by
  induction x using _root_.IGame.ofSetsRecOn with
  | ofSets s t ihs iht =>
      simp only [Game.fromSupport,
        _root_.IGame.ofSetsRecOn_ofSets, Game.toSupport]
      apply _root_.IGame.ext
      intro p
      simp only [_root_.IGame.moves_ofSets]
      cases p
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink s).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ s
          simpa only [ihs y.1 y.2] using y.2
        · intro hz
          let i := equivShrink s ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromSupport] using ihs z hz
      · ext z
        constructor
        · rintro ⟨i, rfl⟩
          let y := (equivShrink t).symm i
          change Game.toSupport (Game.fromSupport y.1) ∈ t
          simpa only [iht y.1 y.2] using y.2
        · intro hz
          let i := equivShrink t ⟨z, hz⟩
          refine ⟨i, ?_⟩
          simpa only [i, Equiv.symm_apply_apply, Game.fromSupport] using iht z hz

end ConwayRefinement.Standalone.InlineConwayRefinement
end
