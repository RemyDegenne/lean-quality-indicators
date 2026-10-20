public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]

variable {FA : A → A → Type*} {CA : A → Type w}

variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]

variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {J : Type wj} [Category.{vj} J] [HasColimitsOfShape J A]

@[simp] theorem limitConeOfSpaceCone_π_mate (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] (i : Jᵒᵖ) :
    sheafMate A ((limitConeOfSpaceCone A S c hc).cone.π.app i) =
      (conePullbackColimitCocone A S c).ι.app (unop i) :=
  pullbackCoconeLeg_mate A S c (conePullbackColimitCocone A S c) i

end AlgebraicGeometry.SheafedSpace
end
end
