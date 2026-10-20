universe u v

open scoped DirectSum

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]

variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

theorem decompose_mul_of_right_mem_eq_zero {r g : R} {e δ : NatOrdinal} (hg : g ∈ 𝒜 e)
    (h : ∀ β, β + e ≠ δ) : (DirectSum.decompose 𝒜 (r * g) δ : R) = 0 := by
  classical
  rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒜 hg,
    DirectSum.coe_mul_apply_eq_dfinsuppSum, DFinsupp.sum_comm]
  refine (DFinsupp.sum_single_index ?_).trans (DFinsupp.sum_eq_zero fun β ↦ ite_eq_right (h β))
  simp

end LoweringDerivation
end
