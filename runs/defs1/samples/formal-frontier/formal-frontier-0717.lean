@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The same zero-or-infinite exponent support product in multiplicative
notation, for use with profinite groups. -/
noncomputable def primewisePadicQuotientModelContinuousMulEquivTopSupport
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤) :
    Multiplicative (primewisePadicQuotientModel.{u} e) ≃ₜ*
      Multiplicative (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1]) :=
  (primewisePadicQuotientModelContinuousAddEquivTopSupport e he).toMultiplicative

end ProfiniteGrp
end
