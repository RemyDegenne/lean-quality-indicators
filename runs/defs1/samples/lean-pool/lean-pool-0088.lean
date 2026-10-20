public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_n_2falsed`. -/
@[expose]
noncomputable def gN2falsed (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2falsed_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_n_2falsed_2 : Nominal.NPrf (.imp ph (.neg ch))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gPm221d ph ps ch hyp_n_2falsed_1
  have p0001 := @gPm221d ph ch ps hyp_n_2falsed_2
  have p0002 := @gImpbid ph ps ch p0000 p0001
  exact p0002

end NFChoice.DirectNominalPrf.WPPReplay
end
