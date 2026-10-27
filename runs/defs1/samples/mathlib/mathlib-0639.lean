@[expose] public section

namespace Mathlib

namespace Ineq

/-- Prints an `Ineq` as the corresponding infix symbol. -/
def toString : Ineq → String
  | eq => "="
  | le => "≤"
  | lt =>

end Ineq
end Mathlib
end
