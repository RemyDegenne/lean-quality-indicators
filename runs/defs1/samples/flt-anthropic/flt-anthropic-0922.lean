namespace P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod

set_option autoImplicit false

noncomputable section

p2m_open

universe u v

namespace MvPolynomial

namespace TruncatedBox

p2m_open

variable (k : Type u) [CommRing k] {ι : Type v} (N : ι → ℕ)

def K : Ideal (MvPolynomial ι k) :=
  Ideal.span (Set.range fun i : ι => (X i : MvPolynomial ι k) ^ N i)

end TruncatedBox
end MvPolynomial
end
end P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod
