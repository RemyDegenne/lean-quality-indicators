namespace P2MW.S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing

open IsLocalRing RingTheory

namespace Ws14Port

universe u v

open IsLocalRing RingTheory RingTheory.Sequence Module

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

set_option autoImplicit false

open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

open MvPowerSeries

p2m_reactivate

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

variable {α β}

theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
    (f g : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (a.sumElim b) (f * g) =
      ∑ q ∈ antidiagonal a, ∑ r ∈ antidiagonal b,
        coeff (q.1.sumElim r.1) f * coeff (q.2.sumElim r.2) g := by
  classical
  rw [coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image,
    Finset.sum_product]

  rintro ⟨⟨q₁, q₂⟩, ⟨r₁, r₂⟩⟩ - ⟨⟨q₁', q₂'⟩, ⟨r₁', r₂'⟩⟩ - h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨hq₁, hr₁⟩ := Finsupp.sumElim_injective2 h₁
  obtain ⟨hq₂, hr₂⟩ := Finsupp.sumElim_injective2 h₂
  exact ⟨⟨hq₁, hq₂⟩, ⟨hr₁, hr₂⟩⟩

end SumRingEquiv
end MvPowerSeries
end
end
end Ws14Port
end P2MW.S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
