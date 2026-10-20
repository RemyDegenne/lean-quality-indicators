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

theorem nb091_wpp_notmem_0106 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ ((synCpw1 (synCpw1 D))).fv := by
  simpa only [nb091AlphaDummy001, fv_syn_cpw1] using (nb091_focused_notmem_0000 D R)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
