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

/-- Checked nominal proof certificate identified upstream as `nb066_alpha_dummy_033`. -/
@[expose]
noncomputable def nb066AlphaDummy033 (x : Var) (R : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb066AlphaDummy026 x R)))).fv ∪
      ((synCcompl (Class.cv (nb066AlphaDummy027 x R)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
