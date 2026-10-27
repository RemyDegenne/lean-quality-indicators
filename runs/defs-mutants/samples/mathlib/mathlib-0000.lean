@[expose] public section

local notation "bxor" => xor

namespace Nat

universe u

variable {m n : ℕ}

attribute [local simp] Nat.add_comm Nat.mul_comm

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => not a && b

end Nat
end
