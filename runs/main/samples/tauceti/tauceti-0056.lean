public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

theorem separable_resolventCubic (p q r : R)
    (h : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).Separable) :
    (resolventCubic p q r).Separable :=
  (separable_resolventCubic_iff p q r).2 h

end TauCeti
end
