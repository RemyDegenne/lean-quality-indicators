set_option warningAsError true

namespace PowerSeries

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

public theorem coeff_negXLogDeriv_convolution (f : (PowerSeries R)ˣ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal (n + 1),
      coeff p.1 (negXLogDeriv f) * coeff p.2 (f : PowerSeries R) =
        -(coeff (n + 1) (f : PowerSeries R) * (n + 1)) := by
  have h := congrArg (coeff (n + 1)) (negXLogDeriv_mul_value f)
  rw [neg_mul, map_neg, coeff_succ_X_mul, coeff_derivative, coeff_mul] at h
  exact h

end PowerSeries
