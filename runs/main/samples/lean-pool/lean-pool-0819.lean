public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.SemanticCore.Lowering

open NFChoice.ReplaySupport

section Coding

variable {S : Fol.Structure LNF} (hH : Fol.allRealizeSentence S LiteralHailperinNF)

theorem mem_sset_singleton (a b : S) :
    Mem S (kPair hH (singleton hH a) b) (sset hH) ↔ Mem S a b :=
  by
  rw [mem_sset]
  constructor
  · intro h
    exact h a ((mem_singleton hH a a).2 rfl)
  · intro hab z hz
    have hza : z = a := (mem_singleton hH a z).1 hz
    simpa [hza] using hab

end Coding
end NFChoice.Foundation.NFStandard
end
