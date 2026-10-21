namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Topology ENNReal NNReal

namespace IsingPerceptron

lemma hasDerivWithinAt_sqrt_comp {H A : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (t*A t) t) (hA : Continuous A)
    {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt (fun a => H (Real.sqrt a)) (A (Real.sqrt a)/2) (Ici 0) a := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hasDerivWithinAt_sqrt_comp_zero hH hA.continuousAt
  · have h := (hH (Real.sqrt a)).comp a (Real.hasDerivAt_sqrt (ne_of_gt ha))
    have hd : Real.sqrt a * A (Real.sqrt a) * (1 / (2*Real.sqrt a)) = A (Real.sqrt a)/2 := by
      field_simp [(Real.sqrt_pos.mpr ha).ne']
    simpa only [Function.comp_def,hd] using h.hasDerivWithinAt (s := Ici 0)

end IsingPerceptron
end
end OAI
