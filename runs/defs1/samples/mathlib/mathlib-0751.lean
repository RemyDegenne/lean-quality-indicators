@[expose] public section

variable {α β : Type*}

open IsAbsoluteValue

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section DivisionRing

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

end DivisionRing
end CauSeq
end
