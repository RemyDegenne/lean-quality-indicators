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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_375`. -/
@[expose]
noncomputable def nb095AlphaDummy375 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy345 D R S_cls E)
          (synWrex (nb095AlphaDummy346 D R S_cls E)
            (Class.cv (nb095AlphaDummy339 D R S_cls E))
            (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
              (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                (synCsn (synC0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
