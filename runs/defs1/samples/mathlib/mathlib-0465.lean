@[expose] public section

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R S A : Type*)

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

open PolyEquivTensor

/-- If `A` is an `R`-algebra, then `A[X]` is an `R[X]` algebra.
This gives a diamond for `Algebra R[X] R[X][X]`, so this is not a global instance. -/
@[reducible] def Polynomial.algebra : Algebra R[X] A[X] :=
  (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ ↦ by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]

end
end
