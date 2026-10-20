public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) [Finite V]

section CommRing

variable [CommRing k]

/-- The grading of the internal shift `P_i{d}`, normalized by
`(P_i{d})_p = (P_i)_{p-d}` and hence `[P_i{1}] = q[P_i]`. -/
noncomputable def zigzagProjectiveShiftGrade (i : V) (d : ℤ) :
    ℤ → Submodule k (zigzagProjective k G i) :=
  Graded.shift (zigzagProjectiveGrade k G i) (-d)

end CommRing
end TauCeti
end
