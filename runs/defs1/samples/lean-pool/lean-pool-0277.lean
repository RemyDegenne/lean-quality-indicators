@[expose] public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N : Nat} [NeZero N]

/-- The minimum circuit size over a complete basis `B` computing `f`.

This natural-valued interface uses completeness to obtain a realizing circuit.
Use `sizeComplexityWithTop` when the basis may be incomplete. -/
noncomputable def sizeComplexity
    (B : Basis) [CompleteBasis B] (f : BitString N → Bool) : Nat := by
  classical
  exact Nat.find (realizationSizesNonempty (B := B) f)

end Circuit
end Complexity
end
