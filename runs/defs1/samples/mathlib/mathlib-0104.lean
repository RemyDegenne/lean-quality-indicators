@[expose] public section

universe u v

open CategoryTheory

attribute [instance] AddGrpCat.str GrpCat.str

attribute [instance] AddCommGrpCat.str CommGrpCat.str

namespace CommGrpCat

/-- Typecheck a `MonoidHom` as a morphism in `CommGrpCat`. -/
@[to_additive /-- Typecheck an `AddMonoidHom` as a morphism in `AddCommGrpCat`. -/]
abbrev ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := CommGrpCat) f

end CommGrpCat
end
