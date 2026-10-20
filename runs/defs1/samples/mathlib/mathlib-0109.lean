@[expose] public section

variable (α : Type*)

open GenContFract

variable {α}

namespace GenContFract

/-- Constructs a generalized continued fraction without fractional part. -/
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩

end GenContFract
end
