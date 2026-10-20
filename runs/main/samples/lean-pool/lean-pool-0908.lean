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

theorem nb095_fresh_692 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy814] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
