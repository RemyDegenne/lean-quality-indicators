public section

namespace TauCeti

namespace IntegralLattice

open Module

theorem isNegDef_negativeA1 : negativeA1.IsNegDef := by
  rw [negativeA1.isNegDef_iff]
  intro x hx
  rw [negativeA1_form_apply]
  nlinarith [sq_pos_of_ne_zero hx]

end IntegralLattice
end TauCeti
end
