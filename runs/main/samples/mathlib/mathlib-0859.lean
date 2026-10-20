@[expose] public section

open Nat

namespace List

namespace Ico

theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b := by
  grind [mem]

end Ico
end List
end
