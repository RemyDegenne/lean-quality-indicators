@[expose] public section

open scoped NumberField

namespace BGS.Markoff

theorem modulus_le_integerNorm_natAbs_of_quotient_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (p : ℕ) (x : 𝓞 K)
    (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hx : Ideal.Quotient.mk P x = 0) (hxne : x ≠ 0) :
    p ≤ (Algebra.norm ℤ x).natAbs := by
  apply Nat.le_of_dvd (integerNorm_natAbs_pos hxne)
  change (p : ℤ).natAbs ∣ (Algebra.norm ℤ x).natAbs
  rw [Int.natAbs_dvd_natAbs]
  simpa using prime_dvd_integerNorm_of_quotient_eq_zero P p x hP hx

end BGS.Markoff
end
