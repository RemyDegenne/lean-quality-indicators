public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

theorem fv_syn_clnimageresfn : (synClnimageresfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimagecrossfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
end
