public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_inss1`. -/
@[expose]
noncomputable def gInss1 (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCin A B) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gElin (.cv x) A B
  have p0001 :=
    @gSimplbi (.classMem (.cv x) (synCin A B)) (.classMem (.cv x) A)
      (.classMem (.cv x) B) p0000
  have p0002 :=
    @gSsriv x (synCin A B) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        aesop)
      p0001
  exact p0002

end NFChoice.DirectNominalPrf.WPPReplay
end
