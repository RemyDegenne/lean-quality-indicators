public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

theorem map_eval_zero_dirichletMeasure_fin_two {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map (fun x ↦ x 0) = betaMeasure (a 0) (a 1) := by
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  rw [map_eval_dirichletMeasure ha 0, Finset.filter_ne', herase, Finset.sum_singleton]

end Probability
end TauCeti
end
end
