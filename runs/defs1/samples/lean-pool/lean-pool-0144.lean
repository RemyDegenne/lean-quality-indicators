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

/-- Checked nominal proof certificate identified upstream as `nb096_alpha_dummy_126`. -/
@[expose]
noncomputable def nb096AlphaDummy126 (D : Class) (R : Class) (q : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb096AlphaDummy119 D R q)))).fv ∪
      ((synCcompl (Class.cv (nb096AlphaDummy120 D R q)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
