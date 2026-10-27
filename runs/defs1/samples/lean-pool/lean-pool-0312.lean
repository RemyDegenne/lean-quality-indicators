public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sbbii`. -/
@[expose]
noncomputable def gSbbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWsb y x ph) (synWsb y x ps)) :=
  by
  have p0000 := @gBiimpi ph ps hyp_sbbii_1
  have p0001 := @gSbimi ph ps x y p0000
  have p0002 := @gBiimpri ph ps hyp_sbbii_1
  have p0003 := @gSbimi ps ph x y p0002
  have p0004 := @gImpbii (synWsb y x ph) (synWsb y x ps) p0001 p0003
  exact p0004

end NFChoice.DirectNominalPrf.WPPReplay
end
