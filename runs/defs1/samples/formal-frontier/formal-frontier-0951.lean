public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- The `k`-submodule of tensors fixed by every coefficientwise conjugation. -/
def fixedSubmodule : Submodule k (L ⊗[k] R) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, coefficientwise (R := R) σ x = x}
  zero_mem' := by simp
  add_mem' hx hy := by intro σ; simp [hx σ, hy σ]
  smul_mem' a x hx := by intro σ; simpa using congrArg (a • ·) (hx σ)

end GaloisDescent
end
