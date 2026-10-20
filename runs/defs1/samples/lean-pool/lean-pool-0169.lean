public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ralimdaa`. -/
@[expose]
noncomputable def gRalimdaa (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (hyp_ralimdaa_1 : Nominal.NPrf (synWnf x ph))
    (hyp_ralimdaa_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWral x A ps) (synWral x A ch))) :=
  by
  have p0000 := @gEx ph (.classMem (.cv x) A) (.imp ps ch) hyp_ralimdaa_2
  have p0001 := @gA2d ph (.classMem (.cv x) A) ps ch p0000
  have p0002 :=
    @gAlimd ph (.imp (.classMem (.cv x) A) ps) (.imp (.classMem (.cv x) A) ch) x
      hyp_ralimdaa_1 p0001
  have p0003 := (Nominal.biimpRefl (synWral x A ps))
  have p0004 := (Nominal.biimpRefl (synWral x A ch))
  have p0005 :=
    @gN3imtr4g ph (.all x (.imp (.classMem (.cv x) A) ps))
      (.all x (.imp (.classMem (.cv x) A) ch)) (synWral x A ps) (synWral x A ch) p0002
      p0003 p0004
  exact p0005

end NFChoice.DirectNominalPrf.WPPReplay
end
