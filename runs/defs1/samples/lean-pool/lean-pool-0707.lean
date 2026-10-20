public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_biadan2`. -/
@[expose]
noncomputable def gBiadan2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biadan2_1 : Nominal.NPrf (.imp ph ps))
    (hyp_biadan2_2 : Nominal.NPrf (.imp ps (synWb ph ch))) :
    Nominal.NPrf (synWb ph (synWa ps ch)) :=
  by
  have p0000 := @gPm471ri ph ps hyp_biadan2_1
  have p0001 := @gPm532i ps ph ch hyp_biadan2_2
  have p0002 := @gBitri ph (synWa ps ph) (synWa ps ch) p0000 p0001
  exact p0002

end NFChoice.DirectNominalPrf.WPPReplay
end
