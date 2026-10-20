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

theorem nb091_fresh_086 (D : Class) (R : Class) :
    (nb091AlphaDummy091 D R) ∉
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy080 D R))).fv) :=
  by
  simpa only [nb091AlphaDummy091] using
    freshVar_not_mem
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy080 D R))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
