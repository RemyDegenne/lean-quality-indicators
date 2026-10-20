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

theorem nb091_distinct_052 (D : Class) (R : Class) :
    (nb091AlphaDummy183 D R) ≠ (nb091AlphaDummy184 D R) := by
  simpa only [nb091AlphaDummy183, nb091AlphaDummy184] using
    (freshVar_injective (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
