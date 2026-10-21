namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Set

open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma integral_unitInterval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ x : I, f (x:ℝ)) = ∫ x in (0:ℝ)..1, f x := by
  rw [unitInterval.volume_def]
  change (∫ x : Set.Icc (0:ℝ) 1, f (x:ℝ) ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc f,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

end CoulombNeumann
end
end OAI
