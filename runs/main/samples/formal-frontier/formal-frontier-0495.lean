public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

variable (otherBasis thirdBasis : Module.Basis indexType K V)

section FieldComparison

variable (F : Type u) [Field F] (W : Type u) [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] (coordinates : Module.Basis indexType F W)

omit [FiniteDimensional F W] in
theorem generalLinearModuleMatrixEquiv_endMatrixLinearEquiv
    (R : Type u) [CommRing R] [Algebra F R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor F W R)) :
    (generalLinearModuleMatrixEquiv F W indexType coordinates R f).val =
      endMatrixLinearEquiv F W indexType coordinates R f.val := rfl

end FieldComparison
end AlgebraicGeometry
end
end
