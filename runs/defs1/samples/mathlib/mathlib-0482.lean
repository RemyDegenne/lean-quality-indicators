@[expose] public section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

open Polynomial Matrix

section

variable {R} [DecidableEq ι]

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set. -/
def Matrix.Represents (A : Matrix ι ι R) (f : Module.End R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f

end
end
