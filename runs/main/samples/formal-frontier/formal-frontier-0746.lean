@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp] theorem pPowerIndex_obj (p : Nat.Primes) (k : ℕᵒᵈ) :
    (pPowerIndex p).obj k = pPowerIndexLevel p (OrderDual.ofDual k) := rfl

end ProfiniteGrp
end
