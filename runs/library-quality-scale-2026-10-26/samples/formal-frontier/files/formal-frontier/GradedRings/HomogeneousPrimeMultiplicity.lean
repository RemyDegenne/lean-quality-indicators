/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.PrimeMultiplicity
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Prime multiplicity on homogeneous localizations

The prime-multiplicity valuation on an ordinary localization restricts to its
degree-zero homogeneous subring.  On a homogeneous fraction `x / p ^ n`, its
value is `exp (n - multiplicity p x)`.
-/

@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace HomogeneousLocalization

variable {A ι σ : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable {p : A}

/-- The prime-multiplicity valuation on the degree-zero homogeneous
localization away from a prime element. -/
noncomputable def awayPrimeMultiplicityValuation (hp : Prime p) :
    Valuation (Away 𝒜 p) ℤᵐ⁰ :=
  (PrimeMultiplicity.awayValuation
      (B := Localization.Away p) hp).comap
    (algebraMap (Away 𝒜 p) (Localization.Away p))

omit [WfDvdMonoid A] in
/-- A homogeneous localization away from a prime in a domain is itself a
domain.  This is kept as an explicit construction because the nonzeroness of
the powers submonoid depends on the supplied primality proof. -/
theorem isDomain_away (hp : Prime p) : IsDomain (Away 𝒜 p) := by
  let _ : IsDomain (Localization.Away p) :=
    IsLocalization.isDomain_localization
      (PrimeMultiplicity.powers_le_nonZeroDivisors hp)
  exact (val_injective (Submonoid.powers p)).isDomain
    (algebraMap (Away 𝒜 p) (Localization.Away p))

@[simp]
theorem awayPrimeMultiplicityValuation_mk {d : ι} (hp : Prime p)
    (hf : p ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d))
    (hx0 : x ≠ 0) :
    awayPrimeMultiplicityValuation 𝒜 hp (Away.mk 𝒜 hf n x hx) =
      exp ((n : ℤ) - multiplicity p x) := by
  rw [awayPrimeMultiplicityValuation, Valuation.comap_apply,
    algebraMap_apply, Away.val_mk]
  simpa only [Localization.mk_eq_mk'_apply] using
    (PrimeMultiplicity.awayValuation_mk_pow_of_ne_zero
      (B := Localization.Away p) hp x hx0 n)

end HomogeneousLocalization
