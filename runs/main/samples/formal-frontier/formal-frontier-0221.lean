open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem monomial_sub_reduceExponent_mem (n : ℕ)
    (d : Fin (n + 1) →₀ ℕ) (p : MinorIndex n) (h : outerExponent n p ≤ d) :
    (monomial d 1 - monomial (reduceExponent n d p) 1 : Source k n) ∈
      hankelIdeal k n := by
  let q := d - outerExponent n p
  have hcancel : q + outerExponent n p = d := tsub_add_cancel_of_le h
  have hreduce : reduceExponent n d p = q + innerExponent n p := rfl
  have hpoly :
      (monomial d 1 - monomial (reduceExponent n d p) 1 : Source k n) =
        monomial q 1 * hankelMinor k n p := by
    rw [hreduce, ← hcancel, monomial_add_one, monomial_add_one, ← mul_sub,
      monomial_outer_sub_inner]
  rw [hpoly]
  exact Ideal.mul_mem_left _ _ (minor_mem k n p)

end
end
end ToricIdeals.RationalNormalCurve
