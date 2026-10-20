public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

variable (R : Type*) [CommSemiring R]

/-- The unblocked grid differential `∂⁻`, as a linear map on `GC⁻` over the polynomial ring. -/
noncomputable def unblockedDifferential :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.lsum (MvPolynomial (Fin n) R) fun x : GridState n =>
    (LinearMap.id :
        MvPolynomial (Fin n) R →ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) R).smulRight
      (G.unblockedDifferentialOnGenerator R x)

end GridDiagram
end TauCeti
end
