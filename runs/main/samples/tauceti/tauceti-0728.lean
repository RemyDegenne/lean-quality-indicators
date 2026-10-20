public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

-- This cannot be a simp lemma because `p` does not occur on the left-hand side.
theorem variance_of_hasLaw_bernoulliMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : I} (hX : HasLaw X Ber((1 : ℝ), 0, p) P) :
    Var[X; P] = (p : ℝ) * (1 - p) := by
  rw [hX.variance_eq, variance_id_bernoulliMeasure]

end Probability
end TauCeti
end
end
