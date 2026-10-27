@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u} [Category.{v} C]

variable {F : J ⥤ C}

section Limit

variable (J C)

variable {J C}

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W

end Limit
end CategoryTheory.Limits
end
end
