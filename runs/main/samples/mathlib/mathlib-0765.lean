@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

variable {P}

namespace IsStrongGenerator

lemma extremalEpi_coproductFrom
    (hP : IsStrongGenerator P) (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    ExtremalEpi (P.coproductFrom X) where
  toEpi := hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f ↦ ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

end IsStrongGenerator
end ObjectProperty
end CategoryTheory
end
