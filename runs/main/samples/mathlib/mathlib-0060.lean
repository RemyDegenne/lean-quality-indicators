@[expose] public section

namespace PNat

open Nat

theorem gcd_mul_lcm (n m : ℕ+) : gcd n m * lcm n m = n * m :=
  Subtype.ext (Nat.gcd_mul_lcm (n : ℕ) (m : ℕ))

end PNat
end
