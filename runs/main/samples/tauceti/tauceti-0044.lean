public section

namespace RingEquiv

open TauCeti

variable {R S : Type*} [Ring R] [Ring S]

theorem card_centralIdempotents_congr (f : R ≃+* S) :
    Nat.card (centralIdempotents R) = Nat.card (centralIdempotents S) :=
  Nat.card_congr (centralIdempotentsCongr f)

end RingEquiv
end
