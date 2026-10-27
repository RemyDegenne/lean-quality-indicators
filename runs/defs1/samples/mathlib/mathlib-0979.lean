@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- If `G : Cocone F ⥤ Cocone F'` preserves initial objects, it preserves colimit cocones. -/
noncomputable def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
  (Cocone.isColimitEquivIsInitial _).symm <| (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

end CategoryTheory.Limits
end
