public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ceqsalv`. -/
@[expose]
noncomputable def gCeqsalv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ceqsalv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ceqsalv_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.imp (.classEq (.cv x) A) ph)) ps) :=
  by
  have p0000 :=
    @gNfv ps x
      (by
        aesop)
  have p0001 :=
    @gCeqsal ph ps x A
      (by
        aesop)
      p0000 hyp_ceqsalv_1 hyp_ceqsalv_2
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
