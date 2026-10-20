@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp] theorem pPowerResidueDiagram_obj (p : Nat.Primes) (k : ℕᵒᵈ) :
    ((pPowerResidueDiagram.{u} p).obj k : Type u) =
      ULift.{u} (Multiplicative (ZMod (p.1 ^ OrderDual.ofDual k))) := rfl

end ProfiniteGrp
end
