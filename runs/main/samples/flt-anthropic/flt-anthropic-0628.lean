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

@[scoped simp]
theorem coeff_sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) (d : α ⊕ β →₀ ℕ) :
    coeff d (sumInvFun α β g) =
      coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)
        (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn) g) :=
  rfl

end SumRingEquiv
end MvPowerSeries
end
end
end Ws14Port
end P2MW.S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
