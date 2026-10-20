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

/-- Checked nominal proof certificate identified upstream as `nb095_alpha_dummy_660`. -/
@[expose]
noncomputable def nb095AlphaDummy660 (x : Var) (D : Class) (R : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv ∪
      ((synCphi (Class.cv (nb095AlphaDummy628 x D R)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
