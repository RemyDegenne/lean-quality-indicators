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

theorem wpp_notmem_0287 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : (alphaDummy004 x y z A B) ∉ (A).fv := by
  exact (focused_notmem_0007 x y z A B dv_A_z)

end CompositionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
