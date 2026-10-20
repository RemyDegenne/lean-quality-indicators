@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [NormalizationMonoid α]

variable [UniqueFactorizationMonoid α]

theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible hp,
    Multiset.nsmul_singleton]

end UniqueFactorizationMonoid
end
