public noncomputable section

open CategoryTheory Coalgebra HopfAlgebra Limits

universe v u

variable {R : Type u} [CommRing R]

namespace CommHopfAlgCat

variable {A B C : CommHopfAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [HopfAlgebra R X]
  [CommRing Y] [HopfAlgebra R Y] [CommRing Z] [HopfAlgebra R Z]

attribute [instance] commRing hopfAlgebra

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

end CommHopfAlgCat
end
