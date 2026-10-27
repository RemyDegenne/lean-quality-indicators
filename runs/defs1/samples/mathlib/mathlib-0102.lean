@[expose] public section

noncomputable section

open Bialgebra Coalgebra Opposite CategoryTheory Limits MonObj

open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace CommBialgCat

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := bialgEquivOfIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

end CommBialgCat
end
end
