@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

/-- The specialized off-diagonal plane polynomial when its parameter is zero. -/
def cageOffDiagonalZeroParameterPolynomial
    {K : Type*} [Field K] (xi eta : K) (d : Nat) : K[X] :=
  (X ^ 2 - C ((cagePulledRadicand xi d).eval 0 +
      (cagePulledRadicand eta d).eval 0)) ^ 2 -
    C (4 * (cagePulledRadicand xi d).eval 0 *
      (cagePulledRadicand eta d).eval 0)

end
end BGS.Markoff
end
