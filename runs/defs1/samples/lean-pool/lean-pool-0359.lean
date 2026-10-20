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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_350`. -/
@[expose]
noncomputable def nb095AlphaDummy350 (u : Var) (S_cls : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb095AlphaDummy347 u S_cls)
            (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))))))).fv ∪ ((synCcompl
          (Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c)))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
