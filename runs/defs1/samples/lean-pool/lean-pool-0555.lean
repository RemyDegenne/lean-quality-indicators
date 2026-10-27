public section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol

open NFChoice.Foundation

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_rexbidv`. -/
@[expose]
noncomputable def gRexbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (dv_ph_x : x ∉ ph.fv) (hyp_ralbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWrex x A ps) (synWrex x A ch))) :=
  by
  have p0000 :=
    @gNfv ph x
      (by
        aesop)
  have p0001 := @gRexbid ph ps ch x A p0000 hyp_ralbidv_1
  exact p0001

end NFChoice.DirectNominalPrf.WPPReplay
end
