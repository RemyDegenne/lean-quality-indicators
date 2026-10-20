public section

open ValuativeRel IsNonarchimedeanLocalField IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem unitFiltration_le_square (h2 : (2 : K) ≠ 0) :
    unitFiltration K (2 * dyadicLevel K h2 + 1) ≤ Subgroup.square Kˣ := by
  rw [square_eq_range_powMonoidHom]
  simpa only [dyadicLevel_def] using unitFiltration_le_range_powMonoidHom_two h2

end TauCeti
end
