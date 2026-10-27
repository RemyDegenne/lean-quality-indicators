public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_xchbinxr`. -/
@[expose]
noncomputable def gXchbinxr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchbinxr_1 : Nominal.NPrf (synWb ph (.neg ps)))
    (hyp_xchbinxr_2 : Nominal.NPrf (synWb ch ps)) : Nominal.NPrf (synWb ph (.neg ch)) :=
  by
  have p0000 := @gBicomi ch ps hyp_xchbinxr_2
  have p0001 := @gXchbinx ph ps ch hyp_xchbinxr_1 p0000
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
