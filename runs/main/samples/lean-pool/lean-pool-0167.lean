public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

theorem fv_syn_cwpppredmemrel (F : Class) (C : Class) :
    (synCwpppredmemrel F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpppredmemrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredfam]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
end
