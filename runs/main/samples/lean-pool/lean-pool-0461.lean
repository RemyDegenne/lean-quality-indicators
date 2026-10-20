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

theorem nb095_fresh_1022 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy505 D R S_cls E) ∉
      (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy505] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
