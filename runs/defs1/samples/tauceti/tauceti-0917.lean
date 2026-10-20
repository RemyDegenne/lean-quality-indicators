public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

/-- The canonical affine open cover of the scheme of a finite fan, indexed by its cones. -/
-- Expose the cover so that its index type is the cone type in importing modules.
@[expose]
noncomputable def affineToricOpenCover : Φ.algebraicRealization.OpenCover :=
  Scheme.Cover.mkOfCovers Φ.cones Φ.affineToricChart Φ.affineToricChartι
    Φ.exists_affineToricChartι_apply_eq

end TauCeti.Toric.Fan
end
