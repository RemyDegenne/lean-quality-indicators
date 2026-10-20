@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

section

variable [(pushforward.{v} φ).IsRightAdjoint]

/-- The pullback functor `SheafOfModules S ⥤ SheafOfModules R` induced by
a morphism of sheaves of rings `S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R`,
defined as the left adjoint functor to the pushforward, when it exists. -/
noncomputable def pullback : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

end
end SheafOfModules
end
