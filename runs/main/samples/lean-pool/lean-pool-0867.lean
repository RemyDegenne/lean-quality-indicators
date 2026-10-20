@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section SourceDivision

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

theorem splitTraceResidueBlockTerm_mem_coverIdeal
    (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree)
    (q : MvPolynomial (Fin 2) K)
    (hq : splitTraceBaseResidueEvaluation sigma q = 0) :
    MvPolynomial.X 0 ^ (ji.2 : ℕ) * MvPolynomial.X 1 ^ (ji.1 : ℕ) *
        splitTracePowerSubstitution (K := K) e d q ∈
      Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  rw [Ideal.mem_span_singleton]
  have hbase : splitTraceCoverPolynomial (1 : K) sigma 1 1 ∣ q := by
    rw [← Ideal.mem_span_singleton]
    exact splitTraceBaseResiduePolynomial_mem_baseCover
      sigma hsigma hnondegenerate q hq
  have hmapped := map_dvd (splitTracePowerSubstitution (K := K) e d) hbase
  rw [splitTracePowerSubstitution_baseCover] at hmapped
  exact dvd_mul_of_dvd_right hmapped
    (MvPolynomial.X 0 ^ (ji.2 : ℕ) * MvPolynomial.X 1 ^ (ji.1 : ℕ))

end SourceDivision
end
end BGS.Markoff
end
