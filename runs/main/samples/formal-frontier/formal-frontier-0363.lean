open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem reduceExponent_preserves_rncExponent (n : ℕ)
    (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) (h : outerExponent n p ≤ d) :
    rncExponent n (reduceExponent n d p) = rncExponent n d := by
  have hcancel : d - outerExponent n p + outerExponent n p = d :=
    tsub_add_cancel_of_le h
  calc
    rncExponent n (reduceExponent n d p) =
        rncExponent n (d - outerExponent n p) +
          rncExponent n (innerExponent n p) := by rw [reduceExponent, map_add]
    _ = rncExponent n (d - outerExponent n p) +
          rncExponent n (outerExponent n p) := by
        rw [rncExponent_outer_eq_inner n p]
    _ = rncExponent n d := by rw [← map_add, hcancel]

end
end
end ToricIdeals.RationalNormalCurve
