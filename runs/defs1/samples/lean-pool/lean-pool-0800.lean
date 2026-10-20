@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Core

namespace Dyadic

/-- Compute sqrt(d) with a target exponent `prec`.
    Returns a Dyadic with exponent `prec` such that result ≤ sqrt(d).

    For d = m * 2^e, we compute:
    - shift = e - 2*prec (to align for sqrt)
    - m' = m * 2^shift (or m / 2^(-shift) if shift < 0)
    - result = floor(sqrt(m')) * 2^prec

    This ensures: result.toRat ≤ sqrt(d.toRat) -/
def sqrtDown (d : Dyadic) (prec : Int) : Dyadic :=
  if d.mantissa < 0 then zero
  else
    let shift := d.exponent - 2 * prec
    let m := if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)
    ⟨intSqrt m, prec⟩

end Dyadic
end LeanCert.Core
end
end
end
end
