public section

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

open TauCeti

section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem intCastLieHom_mulVec_mem_coordinateLattice (M : Matrix n n ℤ) {v : n → ℚ}
    (hv : v ∈ coordinateLattice n) :
    matrixIntCastLieHom ℚ M *ᵥ v ∈ coordinateLattice n := by
  rw [mem_coordinateLattice_iff] at hv ⊢
  choose z hz using hv
  intro a
  refine ⟨∑ b, M a b * z b, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, hz, Matrix.mulVec, dotProduct,
    matrixIntCastLieHom_apply]

end
end Matrix
end
