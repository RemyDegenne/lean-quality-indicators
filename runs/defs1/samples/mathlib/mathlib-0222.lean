@[expose] public section

universe u

open CategoryTheory

attribute [instance] Lat.str

namespace Lat

/-- Turn a morphism in `Lat` back into a `LatticeHom`. -/
abbrev Hom.hom {X Y : Lat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Lat) f

end Lat
end
