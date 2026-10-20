public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)

namespace DescentDatum

variable {p}

section Hom

variable {X Y Z : Over S'}

variable (D : DescentDatum p X) {E : DescentDatum p Y} {F : DescentDatum p Z}

section Inv

variable {D} (f : Hom D E) [IsIso f.hom]

@[simp]
theorem Hom.inv_hom : f.inv.hom = CategoryTheory.inv f.hom :=
  (rfl)

end Inv
end Hom
end DescentDatum
end TauCeti
end
