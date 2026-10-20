@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

theorem tensorSectionHomEquiv_apply (theta : A ⟶ B) (M : Presheaves A)
    (U : Cᵒᵖ) (N : ModuleCat.{u} ((ringPresheaf B).obj U))
    (t : tensorSection A B theta M U ⟶ N) (m : M.obj U) :
    tensorSectionHomEquiv A B theta M U N t m = t (tensorUnitSection A B theta M U m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact ModuleCat.extendRestrictScalarsAdj_homEquiv_apply t m

end RingedSpaces.Modules
end
