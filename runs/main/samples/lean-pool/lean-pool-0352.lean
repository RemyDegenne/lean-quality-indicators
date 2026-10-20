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

theorem nb091_fresh_252 (D : Class) (R : Class) :
    (nb091AlphaDummy181 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy181] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
