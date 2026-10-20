public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u u' v w

variable {D : Type u'} (C : Type u)

namespace InducedQuiver

variable {R : Type w} [CommRing R] {C} [GradedLinearQuiver.{u, v, w} R C] {F : D → C}

variable (R F) in
/-- The **map of total modules of morphisms** of the induced quiver to that of `C`: on the hom
module of `X` and `Y` it is the inclusion of the hom module of `F X.obj` and `F Y.obj`. -/
noncomputable def totalHomMap : TotalHom R (InducedQuiver C F) →ₗ[R] TotalHom R C :=
  letI := Classical.decEq (InducedQuiver C F × InducedQuiver C F)
  DirectSum.toModule R _ _ fun p ↦ homInclusion (R := R) (F p.1.obj) (F p.2.obj)

end InducedQuiver
end TauCeti.GradedLinearQuiver
end
