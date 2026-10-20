@[expose] public section

open Set Function

namespace Quiver

open CategoryTheory

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v} V]

namespace FreeGroupoid

open Quiver

/-- The inclusion of the quiver on `V` to the underlying quiver on `FreeGroupoid V` -/
def of (V) [Quiver V] : V ⥤q Quiver.FreeGroupoid V where
  obj X := ⟨X⟩
  map f := Quot.mk _ f.toPosPath

end FreeGroupoid
end Quiver
end
