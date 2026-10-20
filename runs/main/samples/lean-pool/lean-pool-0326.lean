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

theorem nb095_fresh_846 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy803 D R S_cls E) ∉
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  simpa only [nb095AlphaDummy803] using
    freshVar_not_mem
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
