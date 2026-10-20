public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem normalizedValuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x) :
    normalizedValuation K x = 1 :=
  ((normalizedValuation K).isOfFinOrder hx).eq_one'

end TauCeti
end
end
