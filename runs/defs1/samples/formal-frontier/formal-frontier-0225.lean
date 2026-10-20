@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace AdmissibleLayer

variable {C : Type u} [Category.{v} C] [Abelian C] {B : C} {P : ObjectProperty C}

variable [P.IsClosedUnderSubobjects] [P.IsClosedUnderBinaryProducts]

/-- Intersect the lower endpoint with `D`. The actual quotient-pair map
embeds `U/(L ⊓ D)` into `(U/L) × (B/D)`, proving admissibility. -/
noncomputable def lowerCut (D : Subobject B) (hD : P (cokernel D.arrow))
    (x : AdmissibleLayer P B) : LowerBounded P B D :=
  ⟨{ lower := x.lower ⊓ D
     upper := x.upper
     lower_le_upper := (Subobject.inf_le_left x.lower D).trans x.lower_le_upper
     admissible :=
       P.prop_of_mono
         (Subobject.quotientIntersectionPair x.lower x.upper D x.lower_le_upper)
         (P.prop_prod _ _ x.admissible hD) },
   Subobject.inf_le_right x.lower D⟩

end AdmissibleLayer
end CategoryTheory
end
