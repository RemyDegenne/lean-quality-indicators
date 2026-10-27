public section

open scoped TensorProduct

namespace AlgHom

variable {k L A B : Type*} [Field k] [Field L] [Algebra k L]

variable [Semiring A] [Semiring B] [Algebra k A] [Algebra k B]

variable [IsGalois k L]

variable (F : L ⊗[k] A →ₐ[L] L ⊗[k] B)

variable (hF : ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
  F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
    TensorProduct.map σ.toLinearMap LinearMap.id (F x))

/-- Descent of an algebra morphism commuting with the scalar-factor Galois action.
Its scalar extension is the original morphism. -/
noncomputable def galoisDescend : A →ₐ[k] B := by
  letI := Module.addCommMonoidToAddCommGroup k (M := B)
  exact (AlgEquiv.ofInjective Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)).symm.toAlgHom.comp
      (((F.restrictScalars k).comp Algebra.TensorProduct.includeRight).codRestrict _
        (galoisDescend_mem_range F hF))

end AlgHom
end
