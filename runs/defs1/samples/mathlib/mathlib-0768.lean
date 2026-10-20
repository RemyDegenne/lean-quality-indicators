@[expose] public section

universe v u

open Opposite

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenCoendsOfShape J C]

variable {F}

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenEndsOfShape J C]

variable {F}

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- The chosen end construction as a functor out of the bifunctor category. -/
@[simps]
def chosenEndFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := chosenEnd F
  map f := chosenEnd.map f

end CategoryTheory.Limits
end
