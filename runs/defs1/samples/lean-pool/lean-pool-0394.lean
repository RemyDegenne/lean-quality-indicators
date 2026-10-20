public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_spsbc`. -/
@[expose]
noncomputable def gSpsbc (ph : Wff) (x : Var) (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.imp (.all x ph) (synWsbc A x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gStdpc4 ph x y
  have p0001 := @gSbsbc ph x y
  have p0002 := @gSylib (.all x ph) (synWsb y x ph) (synWsbc (.cv y) x ph) p0000 p0001
  have p0003 := @gDfsbcq ph x (.cv y) A
  have p0004 :=
    @gSyl5ib (.all x ph) (synWsbc (.cv y) x ph) (.classEq (.cv y) A) (synWsbc A x ph)
      p0002 p0003
  have p0005 :=
    @gVtocleg (.imp (.all x ph) (synWsbc A x ph)) y A V
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0004
  exact p0005

end NFChoice.DirectNominalPrf.WPPReplay
end
