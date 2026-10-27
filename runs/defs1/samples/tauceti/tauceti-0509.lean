public section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti.GrpObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {G N : C} [GrpObj G] [GrpObj N]

namespace Action

variable (A : Action G N)

/-- The canonical inclusion `N ⟶ N ⋊ G` of internal groups. -/
noncomputable def inl : Grp.mk N ⟶ A.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage (A.inlNatTrans ≫ A.pointIso.inv)

end Action
end TauCeti.GrpObj
end
