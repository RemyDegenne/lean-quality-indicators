public section

open CategoryTheory Limits Opposite AlgebraicGeometry

open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X V W : Scheme.{u}} (p : V ⟶ X) [IsAffineHom p]

variable {p} {q : W ⟶ X} [IsAffineHom q]

variable (p)

/-- The canonical isomorphism recovering an affine scheme over `X` from its function algebra.
Its forward map is the gluing of the ordinary affine identifications on inverse images. -/
def _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsIso :
    p.pushforwardStructureAlgebra.relativeSpec ≅ V :=
  asIso p.relativeSpecFunctionsToScheme

end
end TauCeti
end
