public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_anbi1d`. -/
@[expose]
noncomputable def gAnbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWa ps th) (synWa ch th))) :=
  by
  have p0000 := @gA1d ph (synWb ps ch) th hyp_bid_1
  have p0001 := @gPm532rd ph th ps ch p0000
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
