public section

noncomputable section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

theorem integrable_map_coe_projIci_iff {E : Type*} [NormedAddCommGroup E]
    [IsFiniteMeasure μ] (l : ℝ) {f : ℝ → E} :
    Integrable f (μ.map fun x : ℝ ↦ (Set.projIci l x : ℝ)) ↔
      Integrable f (μ.restrict (Ioi l)) := by
  rw [map_coe_projIci μ l, integrable_add_measure]
  refine and_iff_right ?_
  by_cases hzero : μ (Iic l) = 0
  · simp [hzero]
  · rw [integrable_smul_measure hzero (measure_ne_top μ (Iic l))]
    exact integrable_dirac (by simp)

end MeasureTheory.Measure
end
end
