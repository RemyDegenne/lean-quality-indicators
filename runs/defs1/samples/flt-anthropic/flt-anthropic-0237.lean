namespace P2MW.S_WeierstrassCurve_finite_rationalHomSet_units

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace RationalHomUnits

p2m_open

p2m_open

section Subst

variable {S : Type*} [CommRing S]

noncomputable def substXY (P Q : S[X][Y]) : S[X][Y] →+* S[X][Y] :=
  eval₂RingHom (eval₂RingHom (C.comp C) P) Q

end Subst
end RationalHomUnits
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_finite_rationalHomSet_units
