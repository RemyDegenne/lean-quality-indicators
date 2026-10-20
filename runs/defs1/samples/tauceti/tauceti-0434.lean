public section

noncomputable section

open Matrix Set

open LinearMap (BilinForm)

open TauCeti (LinearCode)

variable {F ι ι' ρ ρ' σ σ' τ : Type*} [Field F]

namespace TauCeti

namespace LinearCode

/-- Bases of `C` indexed by `ρ` correspond exactly to generator matrices for `C` with row type `ρ`
and linearly independent rows: a basis corresponds to the matrix whose rows are its vectors. -/
def basisEquivFullRankGeneratorMatrix (C : LinearCode F ι) (ρ : Type*) [Fintype ρ] :
    Module.Basis ρ F C ≃ {G : Matrix ρ ι F // C.IsGeneratorMatrix G ∧ LinearIndependent F G.row}
    where
  toFun b := ⟨Matrix.of fun r ↦ (b r : ι → F), isGeneratorMatrix_of_basis b,
    linearIndependent_row_of_basis b⟩
  invFun G := G.2.1.basis G.2.2
  left_inv b := Module.Basis.eq_of_apply_eq fun r ↦ Subtype.ext (by simp)
  right_inv G := Subtype.ext (Matrix.ext fun r i ↦ by simp)

end LinearCode
end TauCeti
end
end
