public noncomputable section

open ContinuousMap

namespace AbstractMeasure

variable {G A R : Type*} [TopologicalSpace G] [TopologicalSpace A]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section Reconstruction

variable [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]

theorem monoidAlgebraHom_eq_ofFiniteCoefficients (c : MonoidAlgebra R A) :
    monoidAlgebraHom c = ofFiniteCoefficients c.coeff := by
  have h : (monoidAlgebraHom : MonoidAlgebra R A →ₐ[R] D(A, R)).toLinearMap =
      ofFiniteCoefficients.comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
    ext a
    simp
  exact LinearMap.congr_fun h c

end Reconstruction
end AbstractMeasure
end
