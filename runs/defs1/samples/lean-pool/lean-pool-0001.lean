@[expose] public section

namespace Complexity

open Complexity.TM

variable {k : ℕ}

variable {M : TM k} {Y : ℕ → List Bool} {inp₀ junkT : Tape} {v H : ℕ}

/-- The tape family the emission phase starts from: `TM.applyTM`'s block blank,
the bookkeeping tapes as given. -/
def emitStart (extras : Fin (3 + (k + 2) + 0) → Tape) : Fin (3 + (k + 2) + 0) → Tape :=
  fun i => if placeWorkInMiddle 3 (k + 2) i then parkedBlank else extras i

end Complexity
end
