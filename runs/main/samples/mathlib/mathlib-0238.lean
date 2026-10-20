@[expose] public section

variable {α β : Type*}

open IsAbsoluteValue

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section Ring

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

local notation "const" => const abv

@[simp, norm_cast]
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl

end Ring
end CauSeq
end
