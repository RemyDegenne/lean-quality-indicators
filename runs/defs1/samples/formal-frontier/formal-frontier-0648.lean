public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- A subalgebra is stable under coefficientwise Galois conjugation. -/
@[expose] def IsStable (P : Subalgebra L (L ⊗[k] R)) : Prop :=
  ∀ (σ : L ≃ₐ[k] L) ⦃x : L ⊗[k] R⦄,
    x ∈ P → coefficientwise (R := R) σ x ∈ P

end GaloisDescent
end
