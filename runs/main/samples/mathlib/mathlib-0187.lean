@[expose] public section

open Polynomial Function AddMonoidAlgebra Finsupp

noncomputable section

variable {R S : Type*}

@[nolint docBlame]
scoped[LaurentPolynomial] notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

open LaurentPolynomial

namespace LaurentPolynomial

section CommSemiring

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

@[simp]
theorem eval₂_toLaurent (p : R[X]) : eval₂ f x (toLaurent p) = Polynomial.eval₂ f x p := by
  unfold eval₂
  rw [← algebraMap_eq_toLaurent, IsLocalization.lift_eq, coe_eval₂RingHom]

end CommSemiring
end LaurentPolynomial
end
end
