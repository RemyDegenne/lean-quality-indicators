@[expose] public section

noncomputable section

namespace BGS.FiniteField

open Polynomial

variable {F : Type*} [Field F]

local instance algebraicClosureDecidableEq :
    DecidableEq (AlgebraicClosure F) := Classical.decEq _

section FiniteBaseField

variable [Fintype F]

section FrobeniusEndomorphism

variable {u v : F} [(legendreWeierstrassCurve u v).IsElliptic]

/-- The single endomorphism used by the integral discriminant proof of Hasse's inequality:
`[t] - [2]Frob`, where `t = q + 1 - #E(F)` is the usual Frobenius trace.

The remaining geometric wall is to construct an isogeny-degree theory strong enough to compute
the degree of this endomorphism as `frobeniusNormForm q t t 2 = 4q - t²`. -/
def legendreHasseWitnessEndomorphism (u v : F)
:
    (legendreAffineOverClosure u v).Point →+
      (legendreAffineOverClosure u v).Point :=
  legendreFrobeniusTrace u v • AddMonoidHom.id _ -
    (2 : ℤ) • legendrePointFrobeniusHom u v

end FrobeniusEndomorphism
end FiniteBaseField
end BGS.FiniteField
end
end
