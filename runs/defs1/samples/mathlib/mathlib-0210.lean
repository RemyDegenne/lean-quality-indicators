@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type v} [Category.{w} J]

namespace GrpCat

variable (F : J ⥤ GrpCat.{u})

section

variable [Small.{u} (Functor.sections (F ⋙ forget GrpCat))]

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive /-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

end
end GrpCat
end
end
