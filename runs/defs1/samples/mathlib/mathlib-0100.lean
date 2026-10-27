@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max'

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

namespace colimitCoconeIsColimit

variable {F} (t : Cocone F)

/-- Auxiliary definition for `colimitCoconeIsColimit`. -/
def descAddMonoidHom : R F →+ t.1 :=
  ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

end colimitCoconeIsColimit
end
end SemiRingCat.FilteredColimits
end
end
