public section

open CategoryTheory TensorProduct

namespace TauCeti.GaloisDescent

universe u

variable {k L M : Type u} [Field k] [Field L] [Algebra k L] [AddCommGroup M]

variable [FiniteDimensional k L] [IsGalois k L] [Module.Finite ℤ M]

variable (rho : Representation ℤ (L ≃ₐ[k] L) M)

/-- The affine group descended from the diagonalizable group `D(M)` along a finite Galois
extension, as an object of the category of finite-type commutative Hopf algebras.

Its coordinate algebra is the invariant subalgebra `(L[M])^{Gal(L/k)}` for the action twisting
both the coefficients and the exponents. -/
@[expose]
noncomputable def descendedCoordinateRing : FiniteTypeCommHopfAlgCat.{u, u} k :=
  FiniteTypeCommHopfAlgCat.of k (groupAlgebraInvariants rho)

end TauCeti.GaloisDescent
end
