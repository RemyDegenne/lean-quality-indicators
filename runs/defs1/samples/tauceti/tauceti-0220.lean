public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Subtracting one identifies the positive unit-filtration quotient
`U(K,n+1) / U(K,n+2)` with `𝓂[K]^(n+1) / 𝓂[K]^(n+2)`. -/
noncomputable def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded K (n + 1) ≃* Multiplicative (MaximalIdealGraded K (n + 1)) :=
  QuotientGroup.liftEquiv
    ((unitFiltration K (n + 2)).subgroupOf (unitFiltration K (n + 1)))
    (unitFiltrationToMaximalIdealGraded_surjective (K := K) n)
    (ker_unitFiltrationToMaximalIdealGraded (K := K) n).symm

end TauCeti
end
end
