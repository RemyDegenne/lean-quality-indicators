@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Colimits

variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y)
  (ModuleCat.restrictScalars (R.map f).hom)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone in the category `PresheafOfModules R` is colimit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : ∀ (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f ↦ (hc X).hom_ext (fun j ↦ by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        dsimp at h₁ h₂ ⊢
        simp only [← reassoc_of% h₁, ← Functor.map_comp, h₂, Hom.naturality]) }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCocone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCocone s)
    intro j
    dsimp
    rw [← hm]
    rfl

end Colimits
end PresheafOfModules
end
