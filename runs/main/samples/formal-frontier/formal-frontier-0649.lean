public section

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

@[simp] theorem restrictedLeadingTermIdeal_bot
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    μ.restrictedLeadingTermIdeal a ham
      (⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) = ⊥ := by
  apply le_antisymm
  · change Ideal.span ((μ.restrictedLeadingTerm a ham) ''
        ((⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) : Set _)) ≤ ⊥
    apply Ideal.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z = 0 := (Submodule.mem_bot _).mp hz
    subst z
    simp
  · exact bot_le

end MonomialOrder
end
