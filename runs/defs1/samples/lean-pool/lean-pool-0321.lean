public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sylanbr`. -/
@[expose]
noncomputable def gSylanbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanbr_1 : Nominal.NPrf (synWb ps ph))
    (hyp_sylanbr_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gBiimpri ps ph hyp_sylanbr_1
  have p0001 := @gSylan ph ps ch th p0000 hyp_sylanbr_2
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
