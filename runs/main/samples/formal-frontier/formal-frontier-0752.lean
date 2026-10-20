@[expose] public section

universe u v

namespace Bass

open scoped Matrix

theorem stableRangeCondition_one_matrix_iff
    {R : Type u} [Ring R] {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    StableRangeCondition (Matrix ι ι R) 1 ↔ StableRangeCondition R 1 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (stableRangeCondition_one_corner
      (Matrix.isIdempotentElem_single_one (R := R) i) h).map_equiv
        (Matrix.singleCornerRingEquiv i)
  · exact stableRangeCondition_one_matrix

end Bass
end
