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

namespace CompositionAlpha

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_073`. -/
@[expose]
def alphaDummy073 (A : Class) (B : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (alphaDummy042 A B))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

end CompositionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
