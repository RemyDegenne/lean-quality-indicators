set_option autoImplicit false

noncomputable section

open MvPowerSeries IsLocalRing DrinfeldCurve

namespace DrinfeldCurve.LocalChart

variable (q : ℕ) [Fact q.Prime]

structure ChartPresentation (O : Type) [CommRing O] (ϖ : O) where
  f : MvPowerSeries (Fin 2) O
  u : MvPowerSeries (Fin 2) O
  v : MvPowerSeries (Fin 2) O
  isUnit_u : IsUnit u
  isUnit_v : IsUnit v
  f_sub_mem : f - drinfeldForm q O ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) O), X 1}) ^ (q + 2)

end DrinfeldCurve.LocalChart
end
