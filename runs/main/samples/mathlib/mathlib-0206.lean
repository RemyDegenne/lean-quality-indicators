@[expose] public section

universe u v

namespace Matrix

open LinearMap Matrix

variable {n : Type u} [DecidableEq n] [Fintype n]

variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

section specialUnitaryGroup

variable (n) (α)

variable {n} {α}

theorem specialUnitaryGroup_le_unitaryGroup : specialUnitaryGroup n α ≤ unitaryGroup n α :=
  inf_le_left

end specialUnitaryGroup
end Matrix
end
