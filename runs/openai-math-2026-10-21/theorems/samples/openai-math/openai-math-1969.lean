namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

namespace NumberTheoryLean.ConditionalPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory

open scoped ENNReal

open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone

open PrimeCumulativeBound PrimeRatioBins RetainedIntervalUpper PrimeCompletedIntervalUpper

open PrimeHistories PrimeKilledChain DerivativeWeights WeightFutureIntegrals

theorem multiplier_valid_antitone {i : Side} {s a t : ℝ} (hs : Valid i s)
    (ha : Valid i.flip a) (ht : Valid i.flip t) (hat : a ≤ t) :
    multiplier i s t ≤ multiplier i s a := by
  have ha0 := valid_pos ha
  have ht0 := valid_pos ht
  have hphi := TwoStepDensityBounds.weight_antitone ha ht hat
  have hq : (t+1)/t ≤ (a+1)/a := by
    rw [add_div,div_self ht0.ne',add_div,div_self ha0.ne']
    exact add_le_add_right (one_div_le_one_div_of_le ha0 hat) 1
  have hqt : 0 ≤ (t+1)/t := by positivity
  have hqa : 0 ≤ (a+1)/a := by positivity
  have hsq : ((t+1)/t)^2 ≤ ((a+1)/a)^2 := by nlinarith
  unfold multiplier
  apply div_le_div_of_nonneg_right _ (weight_pos hs).le
  exact mul_le_mul hsq hphi (weight_pos ht).le (sq_nonneg _)

end NumberTheoryLean.ConditionalPrimeBins
end Erdos970
end OAI
