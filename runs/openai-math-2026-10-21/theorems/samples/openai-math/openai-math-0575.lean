namespace OAI

noncomputable section

namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology NNReal ENNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma decoratedCenteredRoot_measurable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedCenteredRoot ν step n z F) := by
  have hR := decoratedRootPotential_measurable step hs n F hF
  have hE : StronglyMeasurable (fun p : X×(S×DecoratedCascade S n) =>
      Real.exp (z 0*decoratedRootPotential step n F p)) :=
    (hR.const_mul _).exp.stronglyMeasurable
  have hM : Measurable (fun x => ∫ t : S×DecoratedCascade S n,
      Real.exp (z 0*decoratedRootPotential step n F (x,t))
      ∂((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))) :=
    (StronglyMeasurable.integral_prod_right
      (f := fun x t => Real.exp (z 0*decoratedRootPotential step n F (x,t))) hE).measurable
  exact hR.sub ((hM.comp measurable_fst).log.div_const _)

end SphericalPerceptronFreeEnergy
end
end OAI
