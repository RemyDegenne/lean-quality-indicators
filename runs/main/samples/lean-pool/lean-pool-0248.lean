@[expose] public section

noncomputable section

namespace NavierStokes.HarmonicSourceSupport

open Set Function Filter HarmonicFields HarmonicResidual HarmonicCalculus

open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem residualSource_complementJets
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D)
    {I : Type*} (K : PeriodizedWaveBounds.Cells D I)
    (hv : ∀ n i, NonzeroSupported (⋃ a, K.carrier n a) (realCoefficients (b.velocity n i)))
    (hp : ∀ n, NonzeroSupported (⋃ a, K.carrier n a) (realCoefficients (b.pressure n)))
    (j : ℤ) {s : WeightedClasses.StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (he : WeightedClasses.MemClass s w α (excludedSource G A j)) :
    PeriodizedWaveBounds.ComplementJets s w α K.carrier
      (ParticularWaveAssembly.residualSource c u b G A j) := by
  have hg (n : ℕ) (x : D) (hx : ∀ a, x ∉ K.carrier n a) :
      ParticularWaveAssembly.residualSource c u b G A j n =ᶠ[𝓝 x] excludedSource G A j n :=
    residualSource_complement_germ_of_real c u b G A
      ((K.locallyFinite n).isClosed_iUnion (K.closed n)) n (hv n) (hp n) j (by simpa only [
          mem_iUnion, not_exists] using hx)
  constructor
  · intro n x hx hK
    exact ((he.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).congr_of_eventuallyEq
      (hg n x hK)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := he.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro n x hx hK a ha
    rw [PeriodizedWaveBounds.jets_eq_of_germ (hg n x hK) a]
    exact hb n x hx a ha

end NavierStokes.HarmonicSourceSupport
end
end
