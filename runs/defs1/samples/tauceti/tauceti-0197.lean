public section

namespace RingEquiv

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard sesquilinear form, linear in the first argument and twisted by `σ`
in the second. It is Hermitian when `σ` is involutive. -/
noncomputable def sesquilinearForm (σ : R ≃+* R) :
    (ι → R) →ₗ[R] (ι → R) →ₛₗ[(σ : R →+* R)] R := by
  classical
  exact Matrix.toLinearMapₛₗ₂' R (RingHom.id R) (σ : R →+* R) 1

end RingEquiv
end
