@[expose] public section

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section Submodule

section Semiring

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

variable {A}

/-- Given an internal direct sum decomposition of a module `M`, and a basis for each of the
components of the direct sum, the disjoint union of these bases is a basis for `M`. -/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σ i, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

end Semiring
end Submodule
end DirectSum
end
