@[expose] public section

universe v v₁ u u₁

open CategoryTheory Limits

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

section

variable {C : Type u} [SmallCategory.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

/-- (Colimit) cofork which gives a presentation of a presheaf of modules `M` using
coproducts of free presheaves of modules on Yoneda presheaves. -/
noncomputable abbrev freeYonedaCoproductsCokernelCofork :
    CokernelCofork M.toFreeYonedaCoproduct :=
  CokernelCofork.ofπ _ M.toFreeYonedaCoproduct_fromFreeYonedaCoproduct

end
end PresheafOfModules
end
