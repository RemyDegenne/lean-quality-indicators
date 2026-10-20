public section

namespace NumberField.Set

open Filter IsDedekindDomain NumberField TauCeti

open scoped NumberField symmDiff Topology

variable {K : Type*} [Field K] [NumberField K]

variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

theorem hasDirichletDensity_of_finite (hS : S.Finite) : S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_zero_of_eventually_le (C := S.ncard) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact primeIdealZetaSum_le_card_of_finite hS (by linarith)

end NumberField.Set
end
