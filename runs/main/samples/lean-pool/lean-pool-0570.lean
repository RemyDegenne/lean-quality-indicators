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

theorem nb069_fresh_012 :
    (nb069AlphaDummy015) ∉ (((Class.cv (nb069AlphaDummy007))).fv) := by
  simpa only [nb069AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb069AlphaDummy007))).fv) 1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
