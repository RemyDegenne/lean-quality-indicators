set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley

namespace NodeTab

variable {τ : Tag} {s : Fin τ.rank} (T : NodeTab τ s)

theorem fam_hU (j : Fin T.B) : (T.uW j).foldr (refE τ) (alphaF τ s) = alphaF τ s := by
  apply List.ofFn_injective
  rw [ofFn_foldr_refEG]
  exact T.hU1 j

end NodeTab
end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
end
