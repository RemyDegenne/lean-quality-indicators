public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

section Algebraic

variable {H K T : _root_.CommHopfAlgCat.{v} R}

@[simp]
theorem mkQuotient_comp_liftEqualizer {f g : H ⟶ K} (p : K ⟶ T) (hp : f ≫ p = g ≫ p) :
    mkQuotient K (equalizerHopfIdeal f g) ≫ liftEqualizer p hp = p :=
  mkQuotient_comp_liftQuotient _ _ _

end Algebraic
end CommHopfAlgCat
end TauCeti
end
