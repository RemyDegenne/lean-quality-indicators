namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective

set_option autoImplicit false

universe u

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace AlgebraicGeometry

namespace Scheme

namespace TwoAffineOpenCover

namespace GlueInvertible

p2m_open

p2m_open

p2m_reactivate

p2m_reactivate

variable {X : Scheme.{u}} (U0 U1 : X.Opens)
  (hU0 : IsAffineOpen U0) (hU1 : IsAffineOpen U1) (hU01 : IsAffineOpen (U0 ⊓ U1))

variable (P0 : Type u) [AddCommGroup P0] [Module (X.presheaf.obj (op U0)) P0]

variable (P1 : Type u) [AddCommGroup P1] [Module (X.presheaf.obj (op U1)) P1]

variable (σ : letI := (ρ0 U0 U1).hom.toAlgebra; letI := (ρ1 U0 U1).hom.toAlgebra
   ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U0)] P0) ≃ₗ[X.presheaf.obj (op (U0 ⊓ U1))]
     ((X.presheaf.obj (op (U0 ⊓ U1))) ⊗[X.presheaf.obj (op U1)] P1))

abbrev G0 : ModuleCat (X.presheaf.obj (op U0)) :=
  (moduleSpecΓFunctor (R := X.presheaf.obj (op U0))).obj (M0 U0 P0)

end GlueInvertible
end TwoAffineOpenCover
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
