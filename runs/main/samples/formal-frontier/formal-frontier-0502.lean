public section

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a} : Ideal R) R]

theorem existsUnique_restricted_primitive_singleton_division
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal R).radical = IsLocalRing.maximalIdeal R)
    (g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : σ →₀ ℕ =>
      coeff index (g : MvPowerSeries σ R))) = ⊤)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    ∃! qr : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) ×
        adicallyRestrictedSubring (σ := σ) (Ideal.span {a}),
      f = qr.1 * g + qr.2 ∧
        ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
          coeff index (qr.2 : MvPowerSeries σ R) = 0 := by
  classical
  have hg : g ≠ 0 := by
    intro hzero
    have hunit := isUnit_restrictedContentCoefficient_of_primitive a g hprim
    apply hunit.ne_zero
    simp [hzero]
  have hrestricted : IsAdicallyRestricted (Ideal.span {a}) (g : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp g.property
  obtain ⟨p, hcoeff, _, hdivide⟩ :=
    μ.exists_restricted_primitive_division (ι := PUnit.{1}) a ha ham hrad
      (fun _ : PUnit.{1} => (g : MvPowerSeries σ R))
      (fun _ => hrestricted) (fun _ => hprim)
  have hdelta : μ.restrictedLeadingExponent a ham g = μ.degree (p PUnit.unit) :=
    μ.restrictedLeadingExponent_eq_degree_of_primitive_reduction a ham g hprim
      (p PUnit.unit) (hcoeff PUnit.unit)
  have hfrestricted : IsAdicallyRestricted (Ideal.span {a}) (f : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp f.property
  obtain ⟨q, r, hq, hr, hdivision, hzero⟩ := hdivide (f : MvPowerSeries σ R) hfrestricted
  let quotient : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    ⟨q PUnit.unit, (mem_adicallyRestrictedSubring _ _).mpr (hq PUnit.unit)⟩
  let remainder : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    ⟨r, (mem_adicallyRestrictedSubring _ _).mpr hr⟩
  have hdecomp : f = quotient * g + remainder := by
    apply Subtype.ext
    change (f : MvPowerSeries σ R) =
      (quotient : MvPowerSeries σ R) * (g : MvPowerSeries σ R) +
        (remainder : MvPowerSeries σ R)
    simpa [quotient, remainder] using hdivision
  have hcone : ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
      coeff index (remainder : MvPowerSeries σ R) = 0 := by
    intro index hi
    exact hzero index PUnit.unit (by rw [← hdelta]; exact hi)
  refine ⟨(quotient, remainder), ⟨hdecomp, hcone⟩, ?_⟩
  intro pair hpair
  obtain ⟨hquotient, hremainder⟩ :=
    μ.restricted_singleton_division_unique a ham g hg f pair.1 pair.2
      quotient remainder hpair.1 hdecomp hpair.2 hcone
  exact Prod.ext hquotient hremainder

end MonomialOrder
end
