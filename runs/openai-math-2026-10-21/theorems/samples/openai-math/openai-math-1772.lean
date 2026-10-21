namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

open scoped BigOperators Classical

namespace InvariantIsing

theorem cavity_cutoff_replica_error {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F - referenceReplicaMean ν H F| ≤
      4 * M * (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted hH
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F, referenceReplicaMean_eq_tilted ν H hH]
  exact cavity_twoReplica_cutoff_bound (ν.tilted H) s hs F
    (Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable M
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hF σ)) hM hF

end InvariantIsing
end
end OAI
