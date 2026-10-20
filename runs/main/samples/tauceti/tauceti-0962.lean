public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace TauCeti

open scoped nonZeroDivisors ComplexOrder

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

variable {f : IdealArithmeticFunction K} {s : ℂ}

theorem idealTerm_primeIdealPow_eq_mul_cpow_neg (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) (e : ℕ) :
    idealTerm K f s (P.primeIdealPow e) =
      f (P.primeIdealPow e) * ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e := by
  rw [idealTerm_def, P.absNorm_primeIdealPow, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, Complex.cpow_neg]
  ring

end IdealArithmeticFunction
end TauCeti
end
