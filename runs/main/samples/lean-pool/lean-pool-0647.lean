@[expose] public section

section SourceQuantumProjector

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

theorem subProj_mulVec_of_mem_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ H))
    [K.HasOrthogonalProjection] {ψ : H → ℂ}
    (h : (WithLp.toLp 2 ψ : EuclideanSpace ℂ H) ∈ Kᗮ) : subProj K *ᵥ ψ = 0 := by
  have h1 := subProj_mulVec K ψ
  rw [(Submodule.starProjection_apply_eq_zero_iff K).mpr h] at h1
  have h2 : (WithLp.toLp 2 (subProj K *ᵥ ψ) : EuclideanSpace ℂ H)
      = WithLp.toLp 2 (0 : H → ℂ) := by
    rw [h1]
    rfl
  exact WithLp.toLp_injective 2 h2

end QuantumQueryComplexity
end SourceQuantumProjector
end
