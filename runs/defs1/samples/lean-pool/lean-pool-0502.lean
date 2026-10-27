@[expose] public section

open scoped BigOperators ComplexConjugate

open Complex Real NashEmbedding.Sobolev

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- Polynomial and exponential factor in the higher-order multiplication estimate. -/
noncomputable def mt3BStar (k : Nat) : Real :=
  64 * (k : Real) ^ 2 * ((2 : Real) ^ (2 * (k : Real) - 1) - 2)

end NashEmbedding.Sobolev
end
end
