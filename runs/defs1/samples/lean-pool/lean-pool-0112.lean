public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfbi1`. -/
@[expose]
noncomputable def gDfbi1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))) :=
  by
  have p0000 := Nominal.biimpRefl (synWb ph ps)
  have p0001 :=
    @gSimplim (.imp (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.neg (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (synWb ph ps)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gBi3 ph ps
  have p0004 := @gImpi (.imp ph ps) (.imp ps ph) (synWb ph ps) p0003
  have p0005 :=
    @gImpbii (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) p0002 p0004
  exact p0005

end NFChoice.DirectNominalPrf.WPPReplay
end
