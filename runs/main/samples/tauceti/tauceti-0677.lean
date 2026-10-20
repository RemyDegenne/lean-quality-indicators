public section

namespace TauCeti

open MvPolynomial

theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

end TauCeti
end
