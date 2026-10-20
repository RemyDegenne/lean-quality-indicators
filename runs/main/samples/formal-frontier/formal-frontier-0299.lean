@[expose] public section

open CategoryTheory Function Set

open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp] theorem integerCompletionResidue_eta (n : ℕ) [NeZero n]
    (z : ULift.{u} (Multiplicative ℤ)) :
    integerCompletionResidue.{u} n (ProfiniteCompletion.etaFn _ z) =
      Multiplicative.ofAdd (ULift.up (z.down.toAdd : ZMod n)) := by
  change integerCompletionMap
      (ProfiniteGrp.ofFiniteGrp
        (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod n)))))
      (Multiplicative.ofAdd (ULift.up (1 : ZMod n)))
      (ProfiniteCompletion.etaFn _ z) = _
  calc
    _ = (Multiplicative.ofAdd (ULift.up (1 : ZMod n))) ^ z.down.toAdd :=
      integerCompletionMap_eta _ _ z
    _ = _ := by
      apply Multiplicative.toAdd.injective
      apply ULift.down_injective
      simp

end ProfiniteGrp
end
