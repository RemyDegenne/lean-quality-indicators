@[expose] public section

open scoped Polynomial

namespace PowerSeries

variable {A : Type*} [CommRing A]

section IsWeierstrassDivisorAt

variable (g : A⟦X⟧) (I : Ideal A)

namespace IsWeierstrassDivisorAt

variable {g I} (H : g.IsWeierstrassDivisorAt I)

include H

variable (a : A) (f f' : A⟦X⟧)

/-- The remainder `r` in the proof of Weierstrass division. -/
noncomputable def mod [IsPrecomplete I A] : A[X] :=
  (f - g * H.div f).trunc (g.map (Ideal.Quotient.mk I)).order.toNat

end IsWeierstrassDivisorAt
end IsWeierstrassDivisorAt
end PowerSeries
end
