public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_biidd`. -/
@[expose]
noncomputable def gBiidd (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (synWb ps ps)) :=
  by
  have p0000 := @gBiid ps
  have p0001 := @gA1i (synWb ps ps) ph p0000
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
