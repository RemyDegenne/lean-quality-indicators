@[expose] public noncomputable section

universe u v

open Polynomial

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule

variable {x y : PolynomialModule R M} {r : R} {m m₁ m₂ : M}

lemma «exists» {P : PolynomialModule R M → Prop} : (∃ p, P p) ↔ ∃ q, P (ofCoeff R q) :=
  (coeffEquiv R).exists_congr_left

end PolynomialModule
end
