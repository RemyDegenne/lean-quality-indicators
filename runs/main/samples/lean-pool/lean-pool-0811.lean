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

theorem nb093_distinct_099 (A : Class) :
    (nb093AlphaDummy114 A) ≠ (nb093AlphaDummy116 A) := by
  simpa only [nb093AlphaDummy114, nb093AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb093AlphaDummy108 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
