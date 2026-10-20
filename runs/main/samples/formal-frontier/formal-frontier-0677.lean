@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open scoped Topology

universe u v

namespace ValuationRing

variable {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
  [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

theorem principalAdicCompletion_primeHeight_comap
    (K : Type v) [Field K] [Algebra V K] [IsFractionRing V K]
    (a : V) (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V)
    [IsHausdorff (Ideal.span {a}) V]
    (P : PrimeSpectrum (AdicCompletion (Ideal.span {a}) V)) :
    Order.height
        (PrimeSpectrum.comap
          (algebraMap V (AdicCompletion (Ideal.span {a}) V)) P) =
      Order.height P := by
  exact Order.height_orderIso
    (principalAdicCompletionPrimeSpectrumOrderIso K a ha0 ha) P

end ValuationRing
end
end
