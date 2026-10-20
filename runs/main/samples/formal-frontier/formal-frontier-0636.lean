@[expose] public section

open CategoryTheory

universe u u' v w

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})

variable [stageTopologies : ∀ j : J, TopologicalSpace (F.obj j)]

local instance : ∀ j : J, TopologicalSpace ((F ⋙ forget MonCat).obj j) :=
  fun j => stageTopologies j

variable {H : Type u'} [Monoid H] [TopologicalSpace H]

@[simp]
theorem sectionsπ_sectionsLift_apply (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x)
    (j : J) (x : H) :
    sectionsπContinuousMonoidHom F j (sectionsLift F q hq x) = q j x := rfl

end MonCat
end
