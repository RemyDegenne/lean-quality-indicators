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

namespace SingletonImageAlpha

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_047`. -/
@[expose]
def alphaDummy047 (A : Class) : Var :=
  (freshVar (((Class.cv (alphaDummy003 A))).fv ∪ ((Class.cv (alphaDummy000 A))).fv) 1)

end SingletonImageAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
