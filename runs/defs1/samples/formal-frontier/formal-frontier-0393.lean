@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The universe-uniform factor model: an infinite exponent gives an uplifted
p-adic factor, and a finite exponent `n` gives an uplifted `ZMod (p ^ n)`.
The use of `ENat.recTopCoe` keeps the two cases explicit. -/
noncomputable def padicQuotientFactor (p : Nat.Primes) (e : ℕ∞) :
    ProfiniteAddGrp.{u} :=
  ENat.recTopCoe (padicQuotientFactorTop p)
    (padicQuotientFactorNat p) e

end ProfiniteGrp
end
