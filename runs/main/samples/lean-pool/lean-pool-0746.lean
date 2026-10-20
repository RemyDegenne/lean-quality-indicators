public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.SemanticCore.Lowering

open NFChoice.ReplaySupport

open NFChoice.Compiler.NFCompactLeafEndpoints

theorem exists_nin {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S LiteralHailperinNF) (x y : S) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ ¬(Mem S z x ∧ Mem S z y) :=
  by
  have h := formulaHolds_literal_axiom hH .axNin
  simpa [literalAxiomSyntax, literalAxNin, FormulaHolds, lookup, DVec.nth] using h x y

end NFChoice.Foundation.NFStandard
end
