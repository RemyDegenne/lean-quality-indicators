@[expose] public section

open MeasureTheory Real Set

open scoped ENNReal

namespace Feige

namespace Lemma43Endpoints

open ProbabilityTheory TransferStein TransferTestFunctions

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem expMeasure_one_Ici_all (t : ℝ) :
    expMeasure 1 (Ici t) =
      ENNReal.ofReal (if t < 0 then 1 else exp (-t)) := by
  by_cases ht : t < 0
  · rw [ite_eq_left ht]
    have hsub : Ici 0 ⊆ Ici t := fun x hx => le_trans ht.le hx
    have hge : 1 ≤ expMeasure 1 (Ici t) := by
      have hz := ExponentialTransfer.expMeasure_one_Ici
        (x := 0) le_rfl
      norm_num at hz
      rw [← hz]
      exact measure_mono hsub
    have hle : expMeasure 1 (Ici t) ≤ 1 := by
      rw [← measure_univ (μ := expMeasure 1)]
      exact measure_mono (subset_univ _)
    have hone : expMeasure 1 (Ici t) = 1 := le_antisymm hle hge
    rw [hone]
    simp
  · rw [ite_eq_right ht]
    rw [ExponentialTransfer.expMeasure_one_Ici (le_of_not_gt ht)]

end Lemma43Endpoints
end Feige
end
