set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

theorem e6_check_not_succ : ∀ i : Fin Tag.E6.rank,
    List.ofFn (e6Theta0 + Pi.single i 1) ∉ Tag.E6.artifactRoots := by decide +kernel

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min
end
