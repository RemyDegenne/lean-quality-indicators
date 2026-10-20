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

namespace FirstProjectionAlpha

/-- Checked nominal proof certificate identified upstream as `alpha_dummy_004`. -/
@[expose]
def alphaDummy004 (x : Var) (y : Var) (z : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ((synWex z (Wff.classEq (Class.cv x) (synCop (Class.cv y) (Class.cv z))))).fv) 0)

end FirstProjectionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
