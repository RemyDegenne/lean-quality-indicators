public section

namespace TauCeti

open Polynomial

variable {R : Type*}

variable [CommRing R]

theorem _root_.Polynomial.map_psc_of_right_degree_drop {S : Type*} [CommRing S]
    (f : R →+* S) {p q : R[X]} {m n N j : ℕ}
    (hm : (p.map f).natDegree ≤ m) (hn : (q.map f).natDegree ≤ n)
    (hN : n ≤ N) (hjm : j ≤ m) (hjn : j ≤ n) :
    f (psc p q m N j) = f (p.coeff m) ^ (N - n) *
      psc (p.map f) ((q.reductum (n + 1)).map f) m n j := by
  have htrunc : (q.reductum (n + 1)).map f = q.map f := by
    rw [← reductum_map]
    exact reductum_eq_self (by omega)
  rw [htrunc, ← psc_map_map,
    psc_eq_coeff_pow_mul_of_right_degree_drop hm hn hN hjm hjn, coeff_map]

end TauCeti
end
