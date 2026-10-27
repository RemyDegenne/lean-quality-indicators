public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_adantll`. -/
@[expose]
noncomputable def gAdantll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa th ph) ps) ch) :=
  by
  have p0000 := @gSimpr th ph
  have p0001 := @gSylan (synWa th ph) ph ps ch p0000 hyp_adant2_1
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
