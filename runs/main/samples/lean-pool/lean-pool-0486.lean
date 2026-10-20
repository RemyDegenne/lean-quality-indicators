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

theorem nb058_fresh_008 :
    (nb058AlphaDummy006) ∉
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) :=
  by
  simpa only [nb058AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv)
      1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
