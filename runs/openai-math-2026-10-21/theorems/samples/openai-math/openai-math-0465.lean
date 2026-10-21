namespace OAI

section

noncomputable section

open scoped BigOperators

noncomputable section

open MeasureTheory Complex Set Filter

open scoped Topology ComplexConjugate

namespace ThreeTorus

lemma integral_phase_character (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z ∂phaseHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := phaseHaar)
      (fourier_add_half_inv_index hk (by norm_num))

end ThreeTorus
end
end
end
end OAI
