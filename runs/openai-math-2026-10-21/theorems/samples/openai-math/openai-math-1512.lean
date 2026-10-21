namespace OAI

namespace StableCoordinate.DeterminantRing

open MvPolynomial

variable (k : Type*) [CommRing k]

variable {k}

variable {S : Type*} [CommRing S] [Algebra k S]

@[ext] theorem hom_ext {f g : DeterminantRing.C k →ₐ[k] S}
    (ha : f (a k) = g (a k)) (hd : f (d k) = g (d k))
    (hb : f (b k) = g (b k)) (hc : f (c k) = g (c k))
    (hu : f (u k) = g (u k)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact ha
  · exact hd
  · exact hb
  · exact hc
  · exact hu

end StableCoordinate.DeterminantRing
end OAI
