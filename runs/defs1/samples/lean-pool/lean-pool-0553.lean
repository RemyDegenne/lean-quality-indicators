public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ss0`. -/
@[expose]
noncomputable def gSs0 (A : Class) :
    Nominal.NPrf (.imp (synWss A (synC0)) (.classEq A (synC0))) :=
  by
  have p0000 := @gSs0b A
  have p0001 := @gBiimpi (synWss A (synC0)) (.classEq A (synC0)) p0000
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
