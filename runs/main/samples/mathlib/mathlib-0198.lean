@[expose] public section

open Function

namespace Part

variable {α : Type*} {β : Type*} {γ : Type*}

@[simp]
theorem pure_eq_some (a : α) : pure a = some a :=
  rfl

end Part
end
