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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_141`. -/
@[expose]
noncomputable def nb095AlphaDummy141 (D : Class) (R : Class) (S_cls : Class)
    (E : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
