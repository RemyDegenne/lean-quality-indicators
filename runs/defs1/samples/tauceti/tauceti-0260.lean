public section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] [StarRing R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- A permutation as a unitary matrix: `permutationUnitary σ` is the permutation matrix of `σ⁻¹`,
which makes this a homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationUnitary : Equiv.Perm n →* unitaryGroup n R :=
  (permMatrixHom (R := R)).codRestrict _ fun σ => by
    rw [permMatrixHom_apply]
    exact permMatrix_mem_unitaryGroup σ⁻¹

end Matrix
end
