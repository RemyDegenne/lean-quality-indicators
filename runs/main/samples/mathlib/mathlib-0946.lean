@[expose] public section

namespace MvPolynomial

section CommSemiring

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)

end CommSemiring
end MvPolynomial
end
