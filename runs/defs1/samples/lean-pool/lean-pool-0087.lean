public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ssrab2`. -/
@[expose]
noncomputable def gSsrab2 (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWss (synCrab x A ph) A) :=
  by
  have p0000 := (Nominal.classEqRefl (synCrab x A ph))
  have p0001 :=
    @gSsab2 ph x A
      (by
        aesop)
  have p0002 :=
    @gEqsstri (synCrab x A ph) (.cab x (synWa (.classMem (.cv x) A) ph)) A p0000 p0001
  exact p0002

end NFChoice.DirectNominalPrf.WPPReplay
end
