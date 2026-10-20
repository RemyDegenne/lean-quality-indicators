public section

open scoped Matrix

variable {l m n ι : Type*}

namespace TauCeti

/-- The reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which realises conjugation as a
congruence of realifications. -/
def realifyReflection (ι : Type*) [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

end TauCeti
end
