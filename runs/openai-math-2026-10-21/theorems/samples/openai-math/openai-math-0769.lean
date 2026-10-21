namespace OAI

namespace StableCoordinate

namespace WeightedInitial

open MvPolynomial

variable {σ K : Type*} [CommSemiring K]

section Ring

variable {A : Type*} [CommRing A]

lemma Bounded.neg {w : σ → ℤ} {p : MvPolynomial σ A} {d : ℤ}
    (hp : Bounded w p d) : Bounded w (-p) d := by
  intro m hm
  rw [coeff_neg, neg_ne_zero] at hm
  exact hp m hm

end Ring
end WeightedInitial
end StableCoordinate
end OAI
