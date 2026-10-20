set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

local notation "R'" => R ⋙ forget₂ CommRingCat RingCat

local notation "S'" => S ⋙ forget₂ CommRingCat RingCat

noncomputable abbrev pf : PresheafOfModules.{u} R' ⥤ PresheafOfModules.{u} S' :=
  pushforward (R := R') (ringCatHom φ)

end PullbackMonoidal
end PresheafOfModules
