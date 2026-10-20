@[expose] public section

universe u v

namespace Matrix

variable {R : Type u} [Semiring R] {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem isIdempotentElem_single_one (i : ι) :
    IsIdempotentElem (single i i (1 : R)) := by
  simp [IsIdempotentElem]

end Matrix
end
