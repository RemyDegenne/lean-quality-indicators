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

theorem nb066_fresh_024 (x : Var) (R : Class) :
    (nb066AlphaDummy026 x R) ∉
      (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb066AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb066AlphaDummy018 x R))).fv ∪ ((synC1c)).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
