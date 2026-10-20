@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Reduction modulo `p ^ n` on an uplifted p-adic factor. -/
noncomputable def liftedPadicToZModPow (p : Nat.Primes) (n : ℕ) :
    ULift.{u} ℤ_[p.1] →+* ZMod (p.1 ^ n) :=
  (PadicInt.toZModPow n).comp ULift.ringEquiv.toRingHom

end ProfiniteGrp
end
