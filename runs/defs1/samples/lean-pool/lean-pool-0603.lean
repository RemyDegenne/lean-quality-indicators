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

/-- Checked nominal proof certificate identified upstream as `nb058_alpha_dummy_041`. -/
@[expose]
noncomputable def nb058AlphaDummy041 : Var :=
  (freshVar (((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv ∪
      ((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
