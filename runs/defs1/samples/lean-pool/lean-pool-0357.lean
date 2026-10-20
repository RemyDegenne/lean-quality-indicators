@[expose] public section

namespace LowGenus.GenusFourRow095

open Utilities.Certificate

open Utilities

open Finset

open SubdivisionGraph

open WindowProfile

open AtanasovRanganathan.Configurations

open AtanasovRanganathan.Configurations

variable (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)

namespace CaseThree

/-- Excess of arm length `C` over `B`, used in the Case-3 window construction. -/
abbrev Y : ℕ := C length - B length

end CaseThree
end LowGenus.GenusFourRow095
end
