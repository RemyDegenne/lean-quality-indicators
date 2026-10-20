@[expose] public section

noncomputable section

namespace NavierStokes.ParametricModulation

open Set Filter MeasureTheory Function

open scoped Topology ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
theorem centeredSource_contDiffOn
    (f : P × ℝ → ℝ) (m c : P → ℝ) (U : Set P)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ)))
    (hm : ContDiff ℝ ∞ m) (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (centeredSource f m c) (U ×ˢ (univ : Set ℝ)) :=
  (hc.comp contDiff_fst).contDiffOn.mul (hf.sub (hm.comp contDiff_fst).contDiffOn)

end NavierStokes.ParametricModulation
end
end
