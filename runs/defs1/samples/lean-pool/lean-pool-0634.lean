public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_vtoclf`. -/
@[expose]
noncomputable def gVtoclf (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_vtoclf_1 : Nominal.NPrf (synWnf x ps))
    (hyp_vtoclf_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_vtoclf_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_vtoclf_4 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 :=
    @gIsseti x A
      (by
        aesop)
      hyp_vtoclf_2
  have p0001 := @gBiimpd (.classEq (.cv x) A) ph ps hyp_vtoclf_3
  have p0002 := @gEximi (.classEq (.cv x) A) (.imp ph ps) x p0001
  have p0003 := Nominal.mp p0000 p0002
  have p0004 := @gN1936i ph ps x hyp_vtoclf_1 p0003
  have p0005 := @gMpg ph ps x p0004 hyp_vtoclf_4
  exact p0005

end NFChoice.DirectNominalPrf.WPPReplay
end
