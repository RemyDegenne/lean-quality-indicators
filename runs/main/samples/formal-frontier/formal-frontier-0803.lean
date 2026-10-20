@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem liftedPadicQuotientContinuousAddEquivFactor_natCast_mk
    (p : Nat.Primes) (n : ℕ) (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicQuotientContinuousAddEquivFactor p (n : ℕ∞)
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (n : ℕ∞)) x) =
      ULift.up (PadicInt.toZModPow n x.down) := by
  change zmodContinuousAddEquivULift p n
      (liftedPadicQuotientContinuousAddEquivZMod p n
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (n : ℕ∞)) x)) = _
  rw [liftedPadicQuotientContinuousAddEquivZMod_apply,
    liftedPadicQuotientRingEquivZMod_mk]
  rfl

end ProfiniteGrp
end
