public section

open CategoryTheory Limits _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

namespace twoChartModel

/-- The restriction of a function regular wherever `x⁻¹` is to the places at which `x` is a
unit. -/
noncomputable abbrev infinityChartRestriction (x : F) :
    holomorphyRing {P : Place k F | x⁻¹ ∈ P.integers} →ₐ[k]
      holomorphyRing ({P : Place k F | x ∈ P.integers} ∩ {P : Place k F | x⁻¹ ∈ P.integers}) :=
  Subalgebra.inclusion (holomorphyRing_antitone Set.inter_subset_right)

end twoChartModel
end TauCeti.AlgebraicGeometry
end
