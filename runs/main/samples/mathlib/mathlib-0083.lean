@[expose] public section

noncomputable section

open Function LinearMap Matrix Module Set Submodule

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

section MulLinearMapToMatrix

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

open LinearMap

section Fintype

variable [Fintype ι']

variable [Finite κ] [Fintype ι]

namespace Module.Basis

omit [Fintype ι'] in
@[simp]
lemma toMatrix_mulVec_repr [Finite ι'] (m : M) : b'.toMatrix b *ᵥ b.repr m = b'.repr m := by
  classical
  cases nonempty_fintype ι'
  simp [← LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr]

end Module.Basis
end Fintype
end MulLinearMapToMatrix
end
end
