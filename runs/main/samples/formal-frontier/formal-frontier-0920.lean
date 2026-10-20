@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UpperTriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

@[simp] theorem upperTriangularGroupMulEquivAlgHom_entry
    (s : Matrix.UpperTriangularGroup n R) (i j : n) :
    (upperTriangularGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (matrix K n i j)) = s.1 i j := by
  change (upperTriangularFromGL K n R s) (quotient K n (matrix K n i j)) = _
  rw [← AlgHom.comp_apply, upperTriangularFromGL_comp_quotient, evaluate_matrix]

end AlgebraicGeometry
end
end
