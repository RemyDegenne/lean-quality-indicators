@[expose] public section

universe v u

open Opposite

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* C] [Category* J] (F : Jᵒᵖ ⥤ J ⥤ C) [ChosenCoendsOfShape J C]

variable {F}

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/-- A natural transformation of bifunctors induces a map on chosen coends. -/
def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x ↦ (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ ↦ by
    simp [chosenCoend.condition])

end CategoryTheory.Limits
end
