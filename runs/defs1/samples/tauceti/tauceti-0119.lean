public section

open MvPolynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

namespace Projective

variable (W : WeierstrassCurve R) (C : VariableChange R)

/-- The isomorphism of homogeneous coordinate rings `R[X, Y, Z] ⧸ (W) ≃ₐ[R] R[X, Y, Z] ⧸ (C • W)`
induced by the change of variables `C`: the class of `p(X, Y, Z)` goes to the class of
`p(u²X + rZ, u²sX + u³Y + tZ, Z)`. -/
noncomputable def variableChangeEquiv :
    W.toProjective.CoordinateRing ≃ₐ[R] (C • W).toProjective.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ (linearSubstEquiv C) <| by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, linearSubstEquiv_apply,
      linearSubst_polynomial, Ideal.span_singleton_mul_left_unit
      ((C.u.isUnit.pow 6).map MvPolynomial.C)]

end Projective
end WeierstrassCurve
end
