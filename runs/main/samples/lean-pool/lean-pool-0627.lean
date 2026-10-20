section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularControl

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryPulseBounds

open CommonCoverSolve TorusInverse ParticularWaveBounds LabelSumBounds

open scoped Topology ContDiff InnerProductSpace BigOperators

section ReferenceControl

variable {Label : Type} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

theorem selected_copy_smooth (s : StripData P) (F : PhaseConstruction D)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Label → ℕ → Geometry)
    (l : Label) (n : ℕ) (k : Frequency) :
    (PrimaryCopyBridge.copyFrame (nativeFrame (F.frame (l,n)) χ) (g l n) k).SmoothOn
      (phaseNeighborhood s F χ g l n k ×ˢ F.V (l,n)) := by
  change (PrimaryCopyBridge.reindex (F.frame (l,n)) (fun x : P × Plane => χ x.1)).SmoothOn _
  exact PrimaryCopyBridge.reindex_smoothOn _ _ ((selected_frame_jets F).smoothOn (l,n))
    (frameArgument χ).contDiff.contDiffOn (fun z hz => ⟨hz.1.2.1,hz.2⟩)

end ReferenceControl
end NavierStokes.ActualParticularControl
end
end
end
