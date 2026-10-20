@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{w'} D]

namespace GrothendieckTopology

variable (J)

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable (D)

/-- The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
noncomputable def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  J.plusFunctor D ⋙ J.plusFunctor D

end GrothendieckTopology
end CategoryTheory
end
