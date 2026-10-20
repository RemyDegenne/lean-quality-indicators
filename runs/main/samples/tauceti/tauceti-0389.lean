public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem _root_.IntermediateField.IsTotallyRamified.finite
    {L : IntermediateField K (SeparableClosure K)} (h : L.IsTotallyRamified) :
    Module.Finite K L :=
  h.1

end TauCeti
end
end
