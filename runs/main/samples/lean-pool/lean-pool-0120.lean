@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff Interval

namespace NavierStokes.PressureStream

open TransportPrimitive

section GlobalStream

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reconstructed_divergence_zero {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v w : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) (p : ℝ × E) :
    graphDivergence (physicalSpeed d M) v w
      (streamBeta w (streamPotential d a b M v γd))
      (streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd)) p = 0 := by
  by_cases hp : p.1 ≠ 0
  · exact reconstructed_divergence_zero_of_ne ha hab hd v w hγ hs p hp
  · have hp₀ : p.1 = 0 := not_ne_iff.mp hp
    have hpa : p.1 < a := by simpa only [hp₀] using ha
    have hΨs := streamPotential_supported (M := M) ha hab hd v hγ hs
    have hβs := streamBeta_supported hΨs w
    have hγs := streamGamma_supported hΨs (physicalSpeed d M) v
    have hβ := radial_zero_of_lt hβs hpa
    have hDβ := radial_zero_of_lt (radialSupport_fderiv hβs) hpa
    have hDγ := radial_zero_of_lt (radialSupport_fderiv hγs) hpa
    simp only [graphDivergence, graphDr, graphDz, hβ, hDβ, hDγ,
      _root_.zero_apply, zero_div, add_zero]

end GlobalStream
end NavierStokes.PressureStream
end
end
