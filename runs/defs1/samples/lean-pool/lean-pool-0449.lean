@[expose] public section

noncomputable section

namespace NavierStokes.TailGaugePotential

open Set Filter MeasureTheory ProblemStatement

open scoped Topology ContDiff

/-- Translating the radial variable by one makes the anchored integral a
standard radial history on a domain stable under contraction to zero. -/
noncomputable def shiftedRadialDomain : ProfileHistories.RadialDomain where
  carrier := {p | -1 < p.1}
  isOpen := isOpen_lt continuous_const continuous_fst
  scale_mem := by
    intro p hp v hv
    change -1 < v * p.1
    change -1 < p.1 at hp
    by_cases hpos : 0 ≤ p.1
    · exact lt_of_lt_of_le (by norm_num) (mul_nonneg hv.1 hpos)
    · have hneg : p.1 ≤ 0 := le_of_not_ge hpos
      have hle : p.1 ≤ v * p.1 := by
          nlinarith only [hv, hneg, mul_nonneg (sub_nonneg.mpr hv.2) (neg_nonneg.mpr hneg)]
      exact hp.trans_le hle

end NavierStokes.TailGaugePotential
end
end
