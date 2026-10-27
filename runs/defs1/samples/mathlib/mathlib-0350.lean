@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max'

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace CommRingCat.FilteredColimits

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{max v u})

/-- The proposed colimit cocone is a colimit in `CommRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

end
end CommRingCat.FilteredColimits
end
end
