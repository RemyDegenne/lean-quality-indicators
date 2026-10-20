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

theorem nb095_fresh_764 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy759 D R S_cls E) ∉
      (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy759] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
