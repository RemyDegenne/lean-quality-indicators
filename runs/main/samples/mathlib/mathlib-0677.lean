@[expose] public section

open Prod Decidable Function

namespace Nat

theorem pair_eq_of_unpair_eq {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n

end Nat
end
