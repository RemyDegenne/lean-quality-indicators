public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] [EDist X] {p : ℝ≥0∞}

theorem wassersteinEDist_add_rpow_le (hd : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ μ' ν ν' : Measure X) :
    wassersteinEDist p (μ + μ') (ν + ν') ^ p.toReal
      ≤ wassersteinEDist p μ ν ^ p.toReal + wassersteinEDist p μ' ν' ^ p.toReal := by
  simpa only [wassersteinEDist_rpow_eq_transportCost hd hp0 hp]
    using transportCost_add_le _ μ μ' ν ν'

end TauCeti
end
end
