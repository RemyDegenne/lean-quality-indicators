public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_abvor0`. -/
@[expose]
noncomputable def gAbvor0 (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (synWo (.classEq (.cab x ph) (synCvv)) (.classEq (.cab x ph) (synC0))) :=
  by
  have p0000 := @gId ph
  have p0001 := @gVex x
  have p0002 := @gA1i (.classMem (.cv x) (synCvv)) ph p0001
  have p0003 := @gN2thd ph ph (.classMem (.cv x) (synCvv)) p0000 p0002
  have p0004 :=
    @gEqabcdv ph ph x (synCvv)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        aesop)
      p0003
  have p0005 := @gCon3i ph (.classEq (.cab x ph) (synCvv)) p0004
  have p0006 := @gId (.neg ph)
  have p0007 := @gNoel (.cv x)
  have p0008 := @gA1i (.neg (.classMem (.cv x) (synC0))) (.neg ph) p0007
  have p0009 := @gN2falsed (.neg ph) ph (.classMem (.cv x) (synC0)) p0006 p0008
  have p0010 :=
    @gEqabcdv (.neg ph) ph x (synC0)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      p0009
  have p0011 :=
    @gSyl (.neg (.classEq (.cab x ph) (synCvv))) (.neg ph)
      (.classEq (.cab x ph) (synC0)) p0005 p0010
  have p0012 :=
    @gOrri (.classEq (.cab x ph) (synCvv)) (.classEq (.cab x ph) (synC0)) p0011
  exact p0012

end NFChoice.DirectNominalPrf.WPPReplay
end
