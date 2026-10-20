public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elrab`. -/
@[expose]
noncomputable def gElrab (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_elrab_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem A (synCrab x B ph)) (synWa (.classMem A B) ps)) :=
  by
  have p0000 :=
    @gNfcv x A
      (by
        aesop)
  have p0001 :=
    @gNfcv x B
      (by
        aesop)
  have p0002 :=
    @gNfv ps x
      (by
        aesop)
  have p0003 := @gElrabf ph ps x A B p0000 p0001 p0002 hyp_elrab_1
  exact p0003

end NFChoice.DirectNominalPrf.WPPReplay
end
