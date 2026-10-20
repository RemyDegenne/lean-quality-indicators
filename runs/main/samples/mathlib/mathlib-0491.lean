@[expose] public section

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

section SameCycle

variable {f g : Perm α} {p : α → Prop} {x y z : α}

theorem sameCycle_comm : SameCycle f x y ↔ SameCycle f y x :=
  ⟨SameCycle.symm, SameCycle.symm⟩

end SameCycle
end Equiv.Perm
end
