open scoped HahnSeries NatOrdinal

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

theorem series_maximal_finite_support_divisor (b : Series K) :
    ∃ p : FiniteSupportRing (K := K),
      (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p) ∧
      ∀ p' : FiniteSupportRing (K := K),
        (∀ q : FiniteSupportRing (K := K), (q : Series K) ∣ b ↔ q ∣ p') →
        ∃ k : K, k ≠ 0 ∧
          p' = HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k * p := by
  let hgcd := HahnSeries.Nonpositive.finiteSupport_pairwise_gcd_exists
    (G := ℝ) (K := K)
  obtain ⟨a, ha, _⟩ :=
    existsUnique_isSeriesMaximalFiniteSupportDivisor_of_exists_gcd hgcd b
  induction a using Quotient.inductionOn with
  | _ p =>
      obtain ⟨hpSpec, hpUnique⟩ :=
        series_representative_spec_and_uniqueness b p ha
      exact ⟨p, hpSpec, hpUnique⟩

end
end Berarducci
