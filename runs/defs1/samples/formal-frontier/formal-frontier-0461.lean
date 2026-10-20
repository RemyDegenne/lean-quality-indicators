@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The product of residue rings at positive finite exponents and p-adic
integers at infinite exponents. The index types need not be finite. -/
abbrev primewisePadicSupportProduct (e : Nat.Primes → ℕ∞) : Type u :=
  (∀ p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤},
    ULift.{u} (ZMod (p.1.1 ^ (e p.1).toNat))) ×
  (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])

end ProfiniteGrp
end
