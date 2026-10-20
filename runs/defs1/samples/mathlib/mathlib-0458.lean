@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open scoped Classical in
/-- Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx'`. -/
noncomputable def ramificationIdx : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

end
end Ideal
end
