namespace P2MW.S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions

set_option autoImplicit false

open Matrix

namespace LocalGL2

p2m_open

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

section Gates

variable (ϖ : R)

def bigCellWitness : GL (Fin 2) K :=
  ⟨!![1, 0; (algebraMap R K ϖ)⁻¹, 1], !![1, 0; -(algebraMap R K ϖ)⁻¹, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Gates
end LocalGL2
end P2MW.S_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions
