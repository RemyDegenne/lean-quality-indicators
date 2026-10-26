/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.MonicLift
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PerturbedDivision

@[expose] public section

/-!
# Division by restricted divisors with monic first reductions

Monicity of the actual first reductions supplies polynomial lifts with the same
leading exponents. Finite perturbed division then gives an existential division
and an actual coefficientwise leading-cone remainder condition.
-/

set_option warningAsError true

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R] [Fintype ι]
variable (I : Ideal R) [IsAdicComplete I R] (m : MonomialOrder σ)
variable (g : ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)

/-- Existence of division by finitely many restricted divisors whose actual
first reductions are monic. The quotients and remainder are not canonical. -/
theorem exists_restricted_monic_division
    (hg : ∀ i, m.Monic (MvPowerSeries.adicReduction I 1 (g i)))
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
    ∃ (q : ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
      (r : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I),
      f = (∑ i, q i * g i) + r ∧
        ∀ (α : σ →₀ ℕ) (i : ι),
          m.degree (MvPowerSeries.adicReduction I 1 (g i)) ≤ α →
            MvPowerSeries.coeff α (r : MvPowerSeries σ R) = 0 := by
  classical
  have hlift (i : ι) : ∃ b : MvPolynomial σ R,
      MvPolynomial.map (Ideal.Quotient.mk (I ^ 1)) b =
          MvPowerSeries.adicReduction I 1 (g i) ∧
        m.Monic b ∧ m.degree b = m.degree (MvPowerSeries.adicReduction I 1 (g i)) :=
    m.exists_monic_lift (Ideal.Quotient.mk (I ^ 1))
      Ideal.Quotient.mk_surjective _ (hg i)
  choose b hb using hlift
  have hunit (i : ι) : IsUnit (m.leadingCoeff (b i)) := by
    rw [(hb i).2.1]
    exact isUnit_one
  have hagree (i : ι) :
      MvPowerSeries.adicReduction I 1 (MvPowerSeries.polynomialToRestricted I (b i)) =
        MvPowerSeries.adicReduction I 1 (g i) := by
    rw [MvPowerSeries.adicReduction_polynomial]
    exact (hb i).1
  refine ⟨m.restrictedPerturbedDivisionQuotient I b hunit g hagree f,
    m.restrictedPerturbedDivisionRemainder I b hunit g hagree f,
    m.restrictedPerturbedDivision_decomposition I b hunit g hagree f, ?_⟩
  intro α i hi
  rw [← (hb i).2.2] at hi
  exact m.coeff_restrictedPerturbedDivisionRemainder_eq_zero I b hunit g hagree f α i hi

end MonomialOrder
