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

/-- The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`. -/
noncomputable def toSheafification : 𝟭 _ ⟶ sheafification J D :=
  J.toPlusNatTrans D ≫ Functor.whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)

end GrothendieckTopology
end CategoryTheory
end
