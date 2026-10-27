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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_258`. -/
@[expose]
noncomputable def nb095AlphaDummy258 (x : Var) (R : Class) : Var :=
  (freshVar (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
      ((Class.cv (nb095AlphaDummy251 x R))).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
