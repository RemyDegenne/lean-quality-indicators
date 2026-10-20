public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_merlem12`. -/
@[expose]
noncomputable def gMerlem12 (ph : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph) :=
  by
  have p0000 := @gMerlem5 ch ch
  have p0001 := @gMerlem2 ch (.imp (.neg (.neg ch)) ch) th
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gMerlem4 ph (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph)
      (.imp th (.imp (.neg (.neg ch)) ch))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gMerlem11 (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

end NFChoice.DirectNominalPrf.WPPReplay
end
