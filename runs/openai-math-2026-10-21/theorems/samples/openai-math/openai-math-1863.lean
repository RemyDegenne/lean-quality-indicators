namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology NNReal ENNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedLogTotalMoment_integrable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (x : X) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (decoratedWeightedTotal step n F (x,η))))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  have hid := (decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).comp
    (Real.measurable_exp.comp (Real.measurable_log.const_mul a))
  exact hid.integrable_iff.mpr (cascadeLogTotalMoment_integrable n z hz hz0 hz1 a ha)

end SphericalPerceptronFreeEnergy
end
end OAI
