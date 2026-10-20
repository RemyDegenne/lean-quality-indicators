open scoped NatOrdinal

open Ordinal

public noncomputable section

namespace Tests

/-- The successor exponent `omega + 1`. -/
abbrev successorFactorLimitSuccessorExponent : NatOrdinal :=
  successorFactorLimitExponent + (1 : ℕ)

end Tests
end
