@[expose] public section

noncomputable section

open Complex UpperHalfPlane Set Finset Topology Filter Asymptotics

open scoped UpperHalfPlane Topology Nat

variable (z : ℍ)

namespace EisensteinSeries

section bounding_functions

lemma linear_isTheta_left (d : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (fun (c : ℤ) ↦ (c * z + d)) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]

end bounding_functions
end EisensteinSeries
end
end
