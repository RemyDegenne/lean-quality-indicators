@[expose] public section

open Finset

namespace Configuration

variable (P L : Type*) [Membership P L]

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)

variable {P L}

variable (L)

variable (P) {L}

/-- Number of lines through a given point. -/
noncomputable def pointCount (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }

end Configuration
end
