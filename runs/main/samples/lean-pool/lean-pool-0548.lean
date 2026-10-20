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

theorem nb079_focused_notmem_0000 (A : Class) : (nb079AlphaDummy001 A) ∉ A.fv :=
  by
  change freshVar ((A).fv) 1 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => hu)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
