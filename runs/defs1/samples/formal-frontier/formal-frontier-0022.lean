@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- All coefficient-algebra points are naturally Mathlib's matrix special linear
group, with multiplication given by quotient convolution; the comparison uses
`Matrix.SpecialLinearGroup.toGL` and the local GL point equivalence. -/
def specialLinearGroupMulEquivAlgHom :
    Matrix.SpecialLinearGroup n R ≃*
      WithConv (SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) where
  toFun s := WithConv.toConv (specialLinearFromSL K n R s)
  invFun φ := specialLinearToSL K n R φ.ofConv
  left_inv s := specialLinearToSL_fromSL K n R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact specialLinearFromSL_toSL K n R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (specialLinearFromSL K n R (s * t)).comp (quotient K n) =
      ((WithConv.toConv (specialLinearFromSL K n R s) *
        WithConv.toConv (specialLinearFromSL K n R t)).ofConv).comp
          (specialLinearQuotientBialgHom K n).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [specialLinearFromSL_comp_quotient]
    change (generalLinearGroupMulEquivAlgHom K n R
        (Matrix.SpecialLinearGroup.toGL (s * t))).ofConv =
      (WithConv.toConv ((specialLinearFromSL K n R s).comp (quotient K n)) *
        WithConv.toConv ((specialLinearFromSL K n R t).comp (quotient K n))).ofConv
    rw [specialLinearFromSL_comp_quotient, specialLinearFromSL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((generalLinearGroupMulEquivAlgHom K n R).map_mul
        (Matrix.SpecialLinearGroup.toGL s) (Matrix.SpecialLinearGroup.toGL t))

end AlgebraicGeometry
end
end
