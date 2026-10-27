@[expose] public section

open CategoryTheory Limits

universe v u w

noncomputable section

namespace SemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u})

variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]

namespace HasLimits

/-- Construction of a limit cone in `SemiRingCat`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := ↧(Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

end HasLimits
end SemiRingCat
end
end
