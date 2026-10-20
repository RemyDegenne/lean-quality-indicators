public section

namespace NFChoice.SemanticCore

open NFChoice.Foundation

/-- Semantic right-hand side of `[ x / y ] ph`. -/
@[expose]
def _root_.NFChoice.SemanticCore.CvSubstHolds
    (S : Fol.Structure LNF) (v : Var → S) (x y : Var) (p : Wff) : Prop :=
  Wff.Holds S (update v y (v x)) p

end NFChoice.SemanticCore
end
