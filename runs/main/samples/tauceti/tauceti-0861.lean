public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw) {k l : ℕ}

theorem ext_upperMass {L L' : ExchangeableGraphLaw}
    (h : ∀ (k : ℕ) (F : SimpleGraph (Fin k)), L.upperMass F = L'.upperMass F) : L = L' :=
  ext fun k => Measure.ext_of_Ici_of_finite _ _ fun F =>
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h k F)

end ExchangeableGraphLaw
end DenseGraphLimits
end TauCeti
end
end
