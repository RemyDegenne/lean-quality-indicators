public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.SemanticCore.Lowering

open NFChoice.Compiler.NFCompactLeafSemanticAdapters

open NFChoice.Compiler.NFCompactLeafEndpoints

section Satisfaction

variable {S : Fol.Structure LNF} (hNF : Fol.allRealizeSentence S NF)

theorem nf_models_literalHailperin (hNF : Fol.allRealizeSentence S NF) :
    Fol.allRealizeSentence S LiteralHailperinNF :=
  by
  intro f hf
  rcases hf with ⟨name, rfl⟩
  cases name with
  | axExt => exact realizes_literalAxExt hNF
  | axNin => exact realizes_literalAxNin hNF
  | axXp => exact realizes_literalAxXp hNF
  | axCnv => exact realizes_literalAxCnv hNF
  | ax1c => exact realizes_literalAx1c hNF
  | axSset => exact realizes_literalAxSset hNF
  | axSi => exact realizes_literalAxSi hNF
  | axIns2 => exact realizes_literalAxIns2 hNF
  | axIns3 => exact realizes_literalAxIns3 hNF
  | axTypeLower => exact realizes_literalAxTypeLower hNF
  | axSn => exact realizes_literalAxSn hNF

end Satisfaction
end NFChoice.Foundation.NFStandard
end
