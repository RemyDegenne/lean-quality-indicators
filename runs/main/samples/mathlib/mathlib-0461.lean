@[expose] public section

variable {α β : Type*}

open IsAbsoluteValue

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section Ring

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

local notation "const" => const abv

theorem const_add (x y : β) : const (x + y) = const x + const y :=
  rfl

end Ring
end CauSeq
end
