public section

noncomputable section

open scoped Topology NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem StronglyContinuousSemigroup.HasGrowthBound.mono
    {S : StronglyContinuousSemigroup X} {ω M ω' M' : ℝ}
    (hb : S.HasGrowthBound ω M) (hω : ω ≤ ω') (hM : M ≤ M') :
    S.HasGrowthBound ω' M' := by
  refine ⟨hb.one_le.trans hM, fun t ht => ?_⟩
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hb.one_le
  have hexp : Real.exp (ω * t) ≤ Real.exp (ω' * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hω ht)
  exact (hb.bound t ht).trans
    (mul_le_mul hM hexp (Real.exp_nonneg _) (hM_nonneg.trans hM))

end TauCeti.Semigroups
end
end
