public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ecase3`. -/
@[expose]
noncomputable def gEcase3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ecase3_1 : Nominal.NPrf (.imp ph ch)) (hyp_ecase3_2 : Nominal.NPrf (.imp ps ch))
    (hyp_ecase3_3 : Nominal.NPrf (.imp (.neg (synWo ph ps)) ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @gJaoi ph ch ps hyp_ecase3_1 hyp_ecase3_2
  have p0001 := @gPm261i (synWo ph ps) ch p0000 hyp_ecase3_3
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
