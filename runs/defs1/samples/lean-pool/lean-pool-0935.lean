@[expose] public section

open Finset

namespace Utilities

namespace TwoPole

universe u v

/-- Debit the two boundary fluxes from a divisor on the left factor. -/
def debit {G : CFGraph.{u}} (p : TwoPole G) (D : CFDiv G)
    (c₁ c₂ : ℤ) : CFDiv G :=
  D - c₁ • oneChip p.first - c₂ • oneChip p.second

end TwoPole
end Utilities
end
