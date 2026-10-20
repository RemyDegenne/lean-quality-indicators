namespace P2MW.S_PeriodPair_jLattice_surjective

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

set_option maxRecDepth 8000

noncomputable section

p2m_open

namespace ModularCurve

abbrev kwQepw120c_DiscriminantCuspVanishingProp : Prop :=
  kwQepw129c_TopEdgeCuspVanishingProp
    (fun tau => ModularForm.discriminant tau) 0

end ModularCurve
end
end
end
end P2MW.S_PeriodPair_jLattice_surjective
