public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

attribute [instance] PointedWeierstrassChart.baseMap_open PointedWeierstrassChart.equation_elliptic

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

section Point

variable (c : PointedWeierstrassChart π zero) {P : S ⟶ X} (hP : P ≫ π = 𝟙 S)

/-- The section of the projective model of the equation of a chart `c` induced by a section `P` of
`π`: the section `chartPoint` read through `Spec c.ring ≅ c.base` and the isomorphism `modelIso`
with the projective model. -/
noncomputable def modelPoint : Spec c.ring ⟶ c.equation.projModel :=
  c.baseIso.inv ≫ c.chartPoint hP ≫ c.modelIso.hom

end Point
end PointedWeierstrassChart
end TauCeti.AlgebraicGeometry
end
