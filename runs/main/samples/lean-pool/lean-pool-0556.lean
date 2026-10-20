@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

namespace GerverSofa.PartALeanCert

open LeanCert.Core LeanCert.Engine

theorem jacobianRow12_eq : ∀ j : Fin 22,
    intervalJacobian fullExpr (unitBox (n := 22)) cfg (12 : Fin 22) j =
      jacobianCache (12 : Fin 22) j := by decide +kernel

end GerverSofa.PartALeanCert
end
end
end
end
end
end
end
