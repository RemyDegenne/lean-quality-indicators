public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant coordinate map preserves counit and comultiplication. -/
@[expose] def generalLinearDeterminantBialgHom :
    multiplicativeGroupCoordinateRing K →ₐc[K] CoordinateRing K n :=
  BialgHom.ofAlgHom (generalLinearDeterminantCoordinateMap K n)
    (by
      apply generalLinearDeterminant_coordinate_ext K
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
        generalLinearDeterminantCoordinateMap_coordinate,
        generalLinearDeterminant_counit, multiplicativeGroupCoordinate_counit])
    (by
      apply generalLinearDeterminant_coordinate_ext K
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
        multiplicativeGroupCoordinate_comul,
        Algebra.TensorProduct.map_tmul,
        generalLinearDeterminantCoordinateMap_coordinate,
        generalLinearDeterminant_comul])

end AlgebraicGeometry
end
end
