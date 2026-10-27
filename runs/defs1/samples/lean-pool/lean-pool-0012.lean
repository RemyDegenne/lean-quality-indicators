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

/-- Checked nominal proof certificate identified upstream as `nb093_alpha_dummy_157`. -/
@[expose]
noncomputable def nb093AlphaDummy157 (r : Var) (d : Var) : Var :=
  (freshVar (((Class.cv (nb093AlphaDummy147 r d))).fv ∪
      ((Class.cv (nb093AlphaDummy147 r d))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
