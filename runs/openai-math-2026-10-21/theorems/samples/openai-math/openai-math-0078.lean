namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter

open scoped BigOperators

open MeasureTheory Set Filter

open scoped BigOperators

namespace CoulombNeumann

open CoulombAtom

variable {N M : ℕ}

lemma retained_slice_pressure_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun y => ∫ x, retainedPressure b (S (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedPressure_measurable_param b S Prod.fst hS measurable_fst
  have hh : Integrable (fun p : Configuration N × Configuration M =>
      retainedPressure b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    apply hi.bdd_mul hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖retainedPressure b (S p) p.1‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
      rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
      exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b p.1))
  exact hh.integral_prod_right

end CoulombNeumann
end
end OAI
