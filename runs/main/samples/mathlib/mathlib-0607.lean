@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

section PreirreducibleSpace

variable [PreirreducibleSpace X] [Nonempty Y]

namespace RationalMap

lemma toRationalMap_comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    f.toRationalMap.comp g.toRationalMap = (f.comp g).toRationalMap := by
  rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.representative_toRationalMap_equiv _

end RationalMap
end PreirreducibleSpace
end AlgebraicGeometry.Scheme
end
