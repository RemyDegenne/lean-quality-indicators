@[expose] public section

namespace TMB

universe u v

open Multiset Finset

/-- Conjugation by negation. -/
def rawAffineReflection (τ : ℤ → ℤ) : ℤ → ℤ :=
  fun n => -τ (-n)

end TMB
end
