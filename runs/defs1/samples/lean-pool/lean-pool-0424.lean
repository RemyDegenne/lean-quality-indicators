public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_unisng`. -/
@[expose]
noncomputable def gUnisng (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (synCuni (synCsn A)) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gSneq (.cv x) A
  have p0001 := @gUnieqd (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) p0000
  have p0002 := @gId (.classEq (.cv x) A)
  have p0003 :=
    @gEqeq12d (.classEq (.cv x) A) (synCuni (synCsn (.cv x))) (synCuni (synCsn A))
      (.cv x) A p0001 p0002
  have p0004 := @gVex x
  have p0005 := @gUnisn (.cv x) p0004
  have p0006 :=
    @gVtoclg (.classEq (synCuni (synCsn (.cv x))) (.cv x))
      (.classEq (synCuni (synCsn A)) A) x A V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0003 p0005
  exact p0006

end NFChoice.DirectNominalPrf.WPPReplay
end
