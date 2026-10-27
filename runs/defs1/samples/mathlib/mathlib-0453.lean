@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type v} [Category.{w} J]

namespace CommGrpCat

variable (F : J ⥤ CommGrpCat.{u})

section

variable [Small.{u} (Functor.sections (F ⋙ forget CommGrpCat))]

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

end
end CommGrpCat
end
end
