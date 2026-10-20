@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq sq₃}

variable (F sq sq₃)

/-- The functor `F.DescentData' sq sq₃ ⥤ F.DescentData f`. -/
@[simps]
noncomputable def toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f where
  obj D := D.descentData
  map φ :=
    { hom := φ.hom
      comm := comm φ }

end DescentData'
end Pseudofunctor
end CategoryTheory
end
