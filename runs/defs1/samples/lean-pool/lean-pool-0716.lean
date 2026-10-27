public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_simp2lr`. -/
@[expose]
noncomputable def gSimp2lr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th (synWa (synWa ph ps) ch) ta) ps) :=
  by
  have p0000 := @gSimplr ph ps ch
  have p0001 := @gN3ad2ant2 (synWa (synWa ph ps) ch) th ps ta p0000
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
