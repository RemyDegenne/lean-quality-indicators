@[expose] public section

universe u v w

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem liftedPadicChangeUniverseRingEquiv_down (p : Nat.Primes)
    (x : ULift.{u} ℤ_[p.1]) :
    (liftedPadicChangeUniverseRingEquiv.{u,v} p x).down = x.down :=
  rfl

end ProfiniteGrp
end
