@[expose] public section

universe t w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Equalizer

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type (max v u)) {X : C} (R : Presieve X)
  (S : Sieve X)

noncomputable section

variable {P R}

variable (P R)

namespace Presieve

variable [R.HasPairwisePullbacks]

namespace Arrows

variable (P : Cᵒᵖ ⥤ Type w) {X : C} (S : Sieve X)

open Presieve

variable {B : C} {I : Type t} [Small.{w} I] (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks]

/--
The second of the two parallel morphisms of the fork diagram, induced by the second projection in
each pullback.
-/
def secondMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

end Arrows
end Presieve
end
end Equalizer
end CategoryTheory
end
