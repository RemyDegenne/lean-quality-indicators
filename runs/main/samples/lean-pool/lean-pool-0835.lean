@[expose] public section

namespace LocalComplexGeometry

open scoped nonZeroDivisors

noncomputable section

section Prime

variable {n : ℕ} (P : Ideal (HolomorphicGerm (n + 1))) [P.IsPrime]

theorem ambientGermRemainderModMinpolyLiftCertificate_mem_of_coeff_mem
    {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (g : HolomorphicGerm (n + 1)) :
    let C := ambientGermRemainderModMinpolyLiftCertificate
      P a ha ha0 hmem g
    (∀ i, C.coefficients i ∈ lowerDimensionalContraction P) → g ∈ P := by
  dsimp only
  let C := ambientGermRemainderModMinpolyLiftCertificate
    P a ha ha0 hmem g
  intro hcoeff
  change ∀ i, C.coefficients i ∈ lowerDimensionalContraction P at hcoeff
  apply (mem_prime_iff_minpoly_dvd_genericRemainderPolynomial
    P a ha ha0 hmem g).mpr
  exact C.divisible_of_coeff_mem hcoeff

end Prime
end
end LocalComplexGeometry
end
