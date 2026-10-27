@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section Rectangular

variable (R : Type uR) [Semiring R]

variable (ι : Type uι) [Fintype ι] (κ : Type uκ)

variable {S : Type uS} [Semiring S]

/-- Transport a specified right-linear map with finite source along a coefficient
homomorphism. The target coordinates need not be finite. The row-matrix
conversions over the opposite semirings are Mathlib's existing conversions. -/
noncomputable def rightFreeLinearMapScalarExtension
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    (ι → S) →ₗ[Sᵐᵒᵖ] (κ → S) := by
  classical
  exact LinearEquiv.arrowCongrAddEquiv
    (rightFreeCoordEquiv S ι) (rightFreeCoordEquiv S κ)
    (Matrix.toLinearMapRight'
      ((LinearMap.toMatrixRight'
        (LinearEquiv.arrowCongrAddEquiv
          (rightFreeCoordEquiv R ι).symm (rightFreeCoordEquiv R κ).symm g)).map
            (RingHom.op f)))

end Rectangular
end Module
end
