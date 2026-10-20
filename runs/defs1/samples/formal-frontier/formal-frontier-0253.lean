public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- Coefficientwise Galois conjugation on `L ⊗[k] R`. -/
@[expose] noncomputable def coefficientwise (σ : L ≃ₐ[k] L) : L ⊗[k] R →ₐ[k] L ⊗[k] R :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)

end GaloisDescent
end
