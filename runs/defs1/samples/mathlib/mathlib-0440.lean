@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C]

attribute [instance] Grp.grp AddGrp.addGrp

variable
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

namespace Functor

variable {F F' : C ⥤ D} {G : D ⥤ E}

section Monoidal

variable [F.Monoidal] [F'.Monoidal] [G.Monoidal]

open scoped Obj

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.grpObjObj
  CategoryTheory.Functor.addGrpObjObj

open Monoidal

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] Monoidal.ofChosenFiniteProducts in
/-- `mapGrp` is functorial in the left-exact functor. -/
@[to_additive (attr := simps)
/-- `mapAddGrp` is functorial in the left-exact functor. -/]
noncomputable def mapGrpFunctor : (C ⥤ₗ D) ⥤ Grp C ⥤ Grp D where
  obj F := F.1.mapGrp
  map {F G} α := { app A := Grp.homMk'' (α.hom.app A.X) }

end Monoidal
end Functor
end CategoryTheory
end
