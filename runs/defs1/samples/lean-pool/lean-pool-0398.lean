@[expose] public section

open scoped BigOperators ComplexConjugate

open Complex Real NashEmbedding.Sobolev

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The canonical ℂ-linear isomorphism `X_n^* ≃ₗ[ℂ] ℂ^{ℤⁿ}`, sending
`φ` to its Fourier coefficient sequence `m ↦ φ(e_{-m})`.
Every linear functional on `X_n` is determined by its values on the basis
`(eₘ)_{m ∈ ℤⁿ}`, and any choice of values defines a linear functional. -/
def dualEquivSeq (n : ℕ) : TrigPolyDual n ≃ₗ[ℂ] ((Fin n → ℤ) → ℂ) :=
  { toFun := fourierCoeffDistrib
    invFun := seqToDual n
    left_inv := seqToDual_fourierCoeffDistrib
    right_inv := fourierCoeffDistrib_seqToDual
    map_add' := fun φ ψ => by ext m; simp [fourierCoeffDistrib]
    map_smul' := fun c φ => by ext m; simp [fourierCoeffDistrib] }

end NashEmbedding.Sobolev
end
end
