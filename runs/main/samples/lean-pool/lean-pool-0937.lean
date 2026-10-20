@[expose] public section

noncomputable section

namespace NavierStokes.TemporalMeanUpdate

open Set Filter MeasureTheory Function

open TorusInverse

open scoped Topology ContDiff BigOperators Interval

section AxialReconstruction

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem axialUpdate_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) (h : ℝ) (n : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (axialUpdate d a b M v h n f) :=
  PressureStream.streamGamma_supported (axialPotential_supported ha hab hd v h n hf hp hs)
    (PressureStream.physicalSpeed d M) (0, v)

end AxialReconstruction
end NavierStokes.TemporalMeanUpdate
end
end
