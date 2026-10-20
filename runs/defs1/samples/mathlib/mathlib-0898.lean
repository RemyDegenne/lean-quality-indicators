@[expose] public noncomputable section

open Finsupp hiding single

variable {R S G M N O ι : Type*}

macro_rules | `($R[$M]) => `(AddMonoidAlgebra $R $M)

namespace MonoidAlgebra

macro_rules | `($R[$M]) => `(MonoidAlgebra $R $M)

section Semiring

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ m₁' m₂' : M}

section Monoid

variable [Monoid M] [Monoid N]

/-- A product monoid algebra is a nested monoid algebra. -/
@[to_additive (dont_translate := R)
/-- An additive product monoid algebra is a nested additive monoid algebra. -/]
def curryAddEquiv : R[M × N] ≃+ R[N][M] :=
  coeffAddEquiv.trans <| .trans Finsupp.curryAddEquiv <| .trans
    (Finsupp.mapRange.addEquiv coeffAddEquiv.symm) coeffAddEquiv.symm

end Monoid
end Semiring
end MonoidAlgebra
end
