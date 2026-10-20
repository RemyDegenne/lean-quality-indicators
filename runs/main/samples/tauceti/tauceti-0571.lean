@[expose] public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v₁ v₂ u₁ u₂ u₃ u₄

section Prod

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  (W : Type u₂) [Category.{v₂} W] [MonoidalCategory W]
  (C : Type u₃) [EnrichedCategory V C] (D : Type u₄) [EnrichedCategory W D]

variable {V W C D}

lemma eId_prod_eq (X : C × D) :
    eId (V × W) X = (eId V X.1, eId W X.2) :=
  rfl

end Prod
end TauCeti
end
