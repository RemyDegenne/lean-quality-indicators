@[expose] public section

namespace NavierStokes.CommonCoverClass

noncomputable section

open Set Function

open scoped ContDiff BigOperators Topology

open TorusInverse

section BandInputs

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sourceArgument_band_stripped_bound (B : Plane ≃L[ℝ] Plane) {h : ℝ} (hh : 0 ≤ h)
    {n gap D : ℕ} (hn : 4 ≤ n) (hd : gap ≤ D) (center : Plane) (k : Frequency)
    {f : P × Plane → V} (hf : ContDiff ℝ ∞ f) (m p q : ℕ)
    (A α : ℝ) (edge weight : P → ℝ)
    (hb : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤
      A * ChartScales.epsilon h n ^ α * ChartScales.S n ^ p * edge z.1 ^ q * weight z.1) :
    ∀ j ≤ m, ∀ w : Joint P, ‖iteratedFDeriv ℝ j
      (fun z => f (sourceArgument (bandGeometry B h n gap center) k z)) w‖ ≤
        (A * bandArgumentCost B D ^ m) * ChartScales.epsilon h n ^ α *
          ChartScales.S n ^ (p + m) * edge w.1.1 ^ q * weight w.1.1 := by
  intro j hj w
  have ha := sourceArgument_band_jet_bound B hh hn hd center k hf m w
    (fun i hi => hb i hi (sourceArgument (bandGeometry B h n gap center) k w)) j hj
  convert! ha using 1
  simp only [sourceArgument_slow, mul_pow, pow_add]
  ring

end BandInputs
end
end NavierStokes.CommonCoverClass
end
