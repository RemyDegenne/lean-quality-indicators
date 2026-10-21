namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Step

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]

theorem adaptiveSeedLaw_failure (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) (good nextGood : Seed → Prop)
    [DecidablePred good] [DecidablePred nextGood] (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ seed, good seed → (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ q) :
    (adaptiveSeedLaw drawLaw incoming next).real {seed | ¬ nextGood seed} ≤
      incoming.real {seed | ¬ good seed} + q := by
  classical
  rw [adaptiveSeedLaw, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  change (incoming.prod (Measure.pi drawLaw)).real
    {pair : Seed × (∀ seed, Draw seed) | ¬ nextGood (next pair.1 (pair.2 pair.1))} ≤ _
  rw [← finite_integral_test (incoming.prod (Measure.pi drawLaw))
    (fun pair : Seed × (∀ seed, Draw seed) => ¬ nextGood (next pair.1 (pair.2 pair.1)))]
  change (∫ pair : Seed × (∀ seed, Draw seed),
    if ¬ nextGood (next pair.1 (pair.2 pair.1)) then (1 : ℝ) else 0
      ∂incoming.prod (Measure.pi drawLaw)) ≤ _
  rw [integral_prod _ (.of_finite)]
  have hinner (seed : Seed) :
      (∫ draws : ∀ seed, Draw seed, if ¬ nextGood (next seed (draws seed)) then (1 : ℝ) else 0
        ∂Measure.pi drawLaw) = (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} := by
    rw [integral_comp_eval (μ := drawLaw) (i := seed)
      (f := fun draw => if ¬ nextGood (next seed draw) then (1 : ℝ) else 0)
      (measurable_of_finite _).aestronglyMeasurable]
    exact finite_integral_test _ _
  simp_rw [hinner]
  have hpoint (seed : Seed) : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤
      (if ¬ good seed then (1 : ℝ) else 0) + q := by
    by_cases hg : good seed
    · simpa only [hg, not_true_eq_false, ite_false, zero_add] using hstep seed hg
    · have hprob : (drawLaw seed).real {draw | ¬ nextGood (next seed draw)} ≤ 1 := measureReal_le_one
      simpa only [hg, not_false_eq_true, ite_true] using hprob.trans (le_add_of_nonneg_right hq)
  have h := integral_mono (μ := incoming) (.of_finite) (.of_finite) hpoint
  rw [integral_add (.of_finite) (integrable_const _), finite_integral_test,
    integral_const, probReal_univ, one_smul] at h
  exact h

end Step
end EditApproximation
end OAI
