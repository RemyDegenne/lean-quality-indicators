@[expose] public section

namespace CriticalPortraits

open Finset

open scoped BigOperators

variable {d m : ℕ}

/-- The low interval-endpoint value of `x` within its host critical set. -/
noncomputable def loV [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m))))
    (x : ZMod (d * m)) : ℕ :=
  if hx : x ∈ T P then (predIn P x hx).val / m else 0

end CriticalPortraits
end
