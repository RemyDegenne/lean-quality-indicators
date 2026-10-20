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

theorem nb095_fresh_049 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy513 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy513] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
