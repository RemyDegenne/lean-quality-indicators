public section

namespace TauCeti

open Polynomial

lemma sqrt_factorial_mul_sqrt_pi_ne_zero (n : ℕ) :
    Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
  (sqrt_factorial_mul_sqrt_pi_pos n).ne'

end TauCeti
end
