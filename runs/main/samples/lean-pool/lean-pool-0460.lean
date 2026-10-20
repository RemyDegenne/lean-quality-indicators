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

theorem support_mem_0066 (A : Class) :
    (alphaDummy061 A) ∈
      (((synCcompl (Class.cv (alphaDummy061 A)))).fv ∪
        ((synCcompl (Class.cv (alphaDummy062 A)))).fv) :=
  by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end SingletonImageAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
