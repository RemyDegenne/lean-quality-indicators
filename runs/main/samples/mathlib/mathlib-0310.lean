@[expose] public section

open Function

namespace Subtype

variable {α β γ : Sort*} {p q : α → Prop}

theorem coe_injective : Injective (fun (a : Subtype p) ↦ (a : α)) := fun _ _ ↦ Subtype.ext

end Subtype
end
