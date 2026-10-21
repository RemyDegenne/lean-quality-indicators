namespace OAI

section

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem cutoff_loss_ae_eq_frequency {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℝ) :
    cutoffLossDensity b f =ᵐ[μ.prod (volume : Measure Velocity)]
      fun p => f p*KineticCollisionNullSets.frequency b f p := by
  have hl : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  filter_upwards [hl.prod_right_ae] with p hp
  apply cutoffLossDensity_eq_frequency
  have hS : MeasurableSet {q : Velocity × Sphere | ‖p.2-q.1‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hi := hp.indicator hS
  convert hi using 1
  funext q
  by_cases h : ‖p.2-q.1‖ < b
  · rw [Set.indicator_of_mem (show q ∈ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_left h]
    rfl
  · rw [Set.indicator_of_notMem (show q ∉ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_right h,zero_mul]

end BoltzmannNonuniqueness.CollisionCompactness
end
end
end OAI
