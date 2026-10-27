@[expose] public section

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

namespace Functor

variable {D : Type*} [Category* D]

section Reflects

/--
A class describing the property of reflecting effective epimorphisms.
-/
class ReflectsEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphisms if morphisms that are mapped to epimorphisms are
  themselves effective epimorphisms.
  -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi (F.map f) → EffectiveEpi f

end Reflects
end Functor
end CategoryTheory
end
