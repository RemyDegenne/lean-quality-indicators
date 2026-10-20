public section

open CategoryTheory

namespace TauCeti

universe u

namespace SplitMaximalTorus

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R}
    [Algebra.FiniteType R H] {r : ℕ}

section ComapOfIso

variable {L : CommHopfAlgCat.{u} R} [Algebra.FiniteType R L]

@[simp]
theorem comapOfIso_coordinateMap (T : SplitMaximalTorus R L r) (e : H ≅ L) :
    (T.comapOfIso e).coordinateMap = e.hom ≫ T.coordinateMap :=
  (rfl)

end ComapOfIso
end SplitMaximalTorus
end TauCeti
end
