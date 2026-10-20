@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa

namespace PartE

open LeanCert.Core

open LeanCert.Engine

open PartALeanCert

theorem scaledResidualExpr_eval_one (phi theta : ℝ) :
    evalFin (scaledResidualExpr (1 : Fin 2)) ![phi, theta] =
      scaledResidualTwo phi theta := by
  simp [scaledResidualExpr, scaledResidualExprList, scaledResidualTwo, scaledB,
    angleNumerator, angleDenominator, bBase, angleDelta,
    eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
    evalFin, finEnv]; ring

end PartE
end GerverSofa
end
end
end
end
end
end
end
end
