public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_biimprcd`. -/
@[expose]
noncomputable def gBiimprcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpcd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ch (.imp ph ps)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gSyl5ibrcom ch ps ph ch p0000 hyp_biimpcd_1
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
