public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe v

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem orthogonalSpinorNorm_surjective_of_negValue (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
    (hneg : ∃ v, Q v < 0) : Function.Surjective (orthogonalSpinorNorm Q hQ) := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := hneg
  let _ : Invertible (Q v) := (isUnit_iff_ne_zero.mpr (ne_of_lt hv)).invertible
  have hval : orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v)
      = squareClassHom (-1 : ℝˣ) := orthogonalSpinorNorm_reflection_eq_neg_one Q hQ hv
  intro x
  rcases eq_one_or_eq_squareClassHom_neg_one x with h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨QuadraticMap.reflectionOrthogonal Q v, by rw [h, hval]⟩

end CliffordAlgebra
end
