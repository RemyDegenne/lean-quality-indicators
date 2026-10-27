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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_746`. -/
@[expose]
noncomputable def nb095AlphaDummy746 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) : Var :=
  (freshVar (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
          (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
            (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
          (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
