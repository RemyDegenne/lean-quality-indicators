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

theorem nb095_wpp_notmem_0746 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb095AlphaDummy001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0018 D R S_cls E)
      (nb095_compact_fv_empty_0030 D R S_cls E))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end
