public section

namespace NFChoice.Compiler.CompactSyntaxFVExplicit

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

theorem fv_syn_wsfin (M : Class) (N : Class) : (synWsfin M N).fv = (M.fv) ∪ (N.fv) :=
  by
  have fresh_a : freshVar (M.fv ∪ N.fv) 0 ∉ (M.fv ∪ N.fv) :=
    freshVar_not_mem (M.fv ∪ N.fv) 0
  simp only [Finset.mem_union] at fresh_a
  ext u
  simp [synWsfin, fv_syn_cnnc, fv_syn_cpw, fv_syn_cpw1, fv_syn_w3a, fv_syn_wa,
    fv_syn_wex, Wff.fv, Class.fv]

end NFChoice.Compiler.CompactSyntaxFVExplicit
end
