public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {J : Type wj} [Category.{vj} J]

/-- The colimit extension into a competing native cone's sheaf. -/
@[expose] noncomputable def conePullbackLimitSheafMap (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C))
    (Q : Cone S) :
    (TopCat.Sheaf.pullback A (hbase.lift ((forget A).mapCone Q))).obj C.pt.sheaf ⟶
      Q.pt.sheaf :=
  (isColimitOfPreserves
    (TopCat.Sheaf.pullback A (hbase.lift ((forget A).mapCone Q))) hsheaf).desc
    (conePullbackLimitTargetCocone A S C hbase Q)

end AlgebraicGeometry.SheafedSpace
end
end
