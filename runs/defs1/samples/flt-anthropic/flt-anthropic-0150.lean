namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible

set_option autoImplicit false

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace TwoAffineOpenCover

namespace GlueIso

p2m_open

p2m_open

section Chart

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

abbrev ιd : op U ⟶ op (hU.fromSpec ''ᵁ ⊤) := (eqToHom (image_top U hU)).op

end Chart
end GlueIso
end TwoAffineOpenCover
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
