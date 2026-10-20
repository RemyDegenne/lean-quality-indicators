public section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Compiler.CompactSyntaxFVExplicit

open NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Compiler.CoreFVSimp

open NFChoice.DefinitionLeaves.AlphaFocusedSupport

open NFChoice.DefinitionLeaves.AlphaFocusedFV

open NFChoice.DirectNominalPrf

open NFChoice.DirectNominalPrf.Nominal

theorem nb095_distinct_933 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy663 x u D R S_cls f E) ≠
      (nb095AlphaDummy664 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy663, nb095AlphaDummy664] using
    (freshVar_injective
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv)
      (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
