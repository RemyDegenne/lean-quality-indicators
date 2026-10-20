public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

theorem fv_syn_chnbaseresfn (F : Class) : (synChnbaseresfn F).fv = F.fv :=
  by
  ext u
  simp [synChnbaseresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
end
