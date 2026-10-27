public section

open CategoryTheory

universe v u

namespace CategoryTheory.IsMonHom

namespace Characteristic

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {H G : C} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [IsMonHom i] [Mono i] [Characteristic i]

/-- The chosen restriction of an ambient automorphism along a characteristic monomorphism. -/
noncomputable def liftIso (e : Grp.mk G ≅ Grp.mk G) : Grp.mk H ≅ Grp.mk H :=
  (Characteristic.lift (i := i) e).choose

end Characteristic
end CategoryTheory.IsMonHom
end
