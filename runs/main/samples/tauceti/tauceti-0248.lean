public section

noncomputable section

open ValuativeRel

namespace TauCeti.DyadicSqrtFive

@[simp]
theorem normalizedValuation_unitSquareClassRep (c : Fin 3 → ZMod 2) :
    normalizedValuation DyadicSqrtFive (unitSquareClassRep c) = 1 := by
  simp [unitSquareClassRep_def]

end TauCeti.DyadicSqrtFive
end
end
