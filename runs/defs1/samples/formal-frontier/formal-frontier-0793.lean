@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The finite residue branch, bundled as a profinite additive group in the
chosen universe. -/
noncomputable def padicQuotientFactorNat (p : Nat.Primes) (n : ℕ) :
    ProfiniteAddGrp.{u} := by
  letI : CompactSpace (ULift.{u} (ZMod (p.1 ^ n))) :=
    Homeomorph.compactSpace
      (Homeomorph.ulift (X := ZMod (p.1 ^ n))).symm
  letI : TotallyDisconnectedSpace (ULift.{u} (ZMod (p.1 ^ n))) :=
    Homeomorph.totallyDisconnectedSpace
      (Homeomorph.ulift (X := ZMod (p.1 ^ n))).symm
  exact ProfiniteAddGrp.of (ULift.{u} (ZMod (p.1 ^ n)))

end ProfiniteGrp
end
