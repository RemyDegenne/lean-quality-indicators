namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LawCommOnPointsBody

theorem hCO_of_shelf (A : Type) [CommRing A] :
    ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ :=
  fun _ _ _ _ _ _ f W => WeierstrassProjModel.exists_isCoefficientHom W f.toRingHom

end LawCommOnPointsBody
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_schemeHomOver_of_isOriginIdentity
