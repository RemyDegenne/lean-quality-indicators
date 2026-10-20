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

namespace SecondProjectionAlpha

theorem support_mem_0060 :
    alphaDummy057 ∈
      (((Class.cv alphaDummy056)).fv ∪ ((Class.cv alphaDummy057)).fv) :=
  by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end SecondProjectionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
