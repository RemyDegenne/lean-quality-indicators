@[expose] public section

open CategoryTheory Function Set

open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The continuous additive residue map from the completed integers at a
positive modulus, written multiplicatively. -/
noncomputable def integerCompletionResidueHom (n : ℕ) [NeZero n] :
    integerCompletion.{u} ⟶
      ProfiniteGrp.ofFiniteGrp
        (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod n)))) :=
  integerCompletionMap _ (Multiplicative.ofAdd (ULift.up (1 : ZMod n)))

end ProfiniteGrp
end
